-- | Circle Pack + Force Demo
-- |
-- | Demonstrates:
-- | - Fetching data from backend API (packages + modules)
-- | - Using hylograph-layout's packSiblingsMap for circle packing within packages
-- | - Using hylograph-simulation for force-directed positioning of packages
-- |
-- | Note: Rendering is now handled externally (via HATS or any other approach).
-- | This test focuses on the simulation physics - it logs node positions.
module Test.CirclePackForceDemo where

import Prelude

import Affjax.Web as AX
import Affjax.ResponseFormat as ResponseFormat
import Data.Argonaut (class DecodeJson, decodeJson, (.:), (.:?))
import Data.Argonaut as Json
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Int (toNumber)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Nullable as Nullable
import Data.Number (sqrt)
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)

-- Hylograph Simulation
import Hylograph.Simulation
  ( runSimulation
  , Engine(..)
  , SimulationEvent(..)
  , subscribe
  , setup
  , collide
  , manyBody
  , center
  , withStrength
  , withRadius
  , withX
  , withY
  , static
  , dynamic
  )
import Hylograph.ForceEngine.Simulation (SimulationNode)

-- Circle packing from hylograph-layout
import DataViz.Layout.Hierarchy.Pack (packSiblingsMap, Circle)

-- =============================================================================
-- API Types
-- =============================================================================

-- | Package from API (wrapped for DecodeJson instance)
newtype APIPackage = APIPackage
  { id :: Int
  , name :: String
  , source :: String
  , moduleCount :: Int
  }

-- | Module from API (wrapped for DecodeJson instance)
newtype APIModule = APIModule
  { id :: Int
  , name :: String
  , package :: { id :: Int, name :: String }
  }

-- | API response wrappers
newtype PackagesResponse = PackagesResponse { packages :: Array APIPackage }
newtype ModulesResponse = ModulesResponse { modules :: Array APIModule }

instance decodePackagesResponse :: DecodeJson PackagesResponse where
  decodeJson json = do
    obj <- Json.toObject json # note "Expected object"
    packages <- obj .: "packages"
    pure $ PackagesResponse { packages }
    where
    note msg Nothing = Left (Json.TypeMismatch msg)
    note _ (Just x) = Right x

instance decodeModulesResponse :: DecodeJson ModulesResponse where
  decodeJson json = do
    obj <- Json.toObject json # note "Expected object"
    modules <- obj .: "modules"
    pure $ ModulesResponse { modules }
    where
    note msg Nothing = Left (Json.TypeMismatch msg)
    note _ (Just x) = Right x

instance decodeAPIPackage :: DecodeJson APIPackage where
  decodeJson json = do
    obj <- Json.toObject json # note "Expected object"
    id <- obj .: "id"
    name <- obj .: "name"
    source <- obj .: "source"
    moduleCount <- obj .: "moduleCount"
    pure $ APIPackage { id, name, source, moduleCount }
    where
    note msg Nothing = Left (Json.TypeMismatch msg)
    note _ (Just x) = Right x

instance decodeAPIModule :: DecodeJson APIModule where
  decodeJson json = do
    obj <- Json.toObject json # note "Expected object"
    id <- obj .: "id"
    name <- obj .: "name"
    pkgObj <- obj .: "package"
    pkgId <- pkgObj .: "id"
    pkgName <- pkgObj .: "name"
    pure $ APIModule { id, name, package: { id: pkgId, name: pkgName } }
    where
    note msg Nothing = Left (Json.TypeMismatch msg)
    note _ (Just x) = Right x

-- =============================================================================
-- Visualization Types
-- =============================================================================

-- | Module circle (packed within a package)
type ModuleCircle =
  { id :: Int
  , name :: String
  , x :: Number      -- Position relative to package center
  , y :: Number
  , r :: Number
  }

-- | Package node for force simulation
-- | Contains pre-packed module circles
type PackageNode = SimulationNode
  ( name :: String
  , source :: String
  , moduleCount :: Int
  , r :: Number                    -- Enclosing radius from circle packing
  , modules :: Array ModuleCircle  -- Pre-packed module positions
  )

-- =============================================================================
-- Data Fetching
-- =============================================================================

apiBaseUrl :: String
apiBaseUrl = "http://localhost:3000"

fetchPackages :: Aff (Either String (Array APIPackage))
fetchPackages = do
  result <- AX.get ResponseFormat.json (apiBaseUrl <> "/api/v2/packages")
  pure $ case result of
    Left err -> Left $ AX.printError err
    Right response -> case decodeJson response.body of
      Left decodeErr -> Left $ Json.printJsonDecodeError decodeErr
      Right (PackagesResponse { packages }) -> Right packages

fetchModules :: Aff (Either String (Array APIModule))
fetchModules = do
  result <- AX.get ResponseFormat.json (apiBaseUrl <> "/api/v2/modules")
  pure $ case result of
    Left err -> Left $ AX.printError err
    Right response -> case decodeJson response.body of
      Left decodeErr -> Left $ Json.printJsonDecodeError decodeErr
      Right (ModulesResponse { modules }) -> Right modules

-- =============================================================================
-- Circle Packing
-- =============================================================================

-- | Group modules by package ID
groupModulesByPackage :: Array APIModule -> Map Int (Array APIModule)
groupModulesByPackage modules =
  foldl addModule Map.empty modules
  where
  addModule acc mod@(APIModule m) =
    Map.alter (Just <<< Array.cons mod <<< fromMaybe []) m.package.id acc

-- | Create a packed package from API data
createPackedPackage :: Int -> APIPackage -> Array APIModule -> PackageNode
createPackedPackage idx (APIPackage pkg) modules =
  let
    -- Create circles for each module (radius based on name length as proxy for size)
    moduleCircles :: Array Circle
    moduleCircles = modules # map \(APIModule m) ->
      { x: 0.0
      , y: 0.0
      , r: 5.0 + sqrt (toNumber (String.length m.name)) * 1.5
      }

    -- Pack the modules using hylograph-layout
    packed = packSiblingsMap moduleCircles

    -- Convert to ModuleCircle with IDs
    packedModules :: Array ModuleCircle
    packedModules = Array.zipWith toModuleCircle modules packed.circles

    -- Initial position in grid
    cols = 8
    row = idx / cols
    col = idx `mod` cols
    x = (toNumber col - 4.0) * 120.0
    y = (toNumber row - 3.0) * 120.0

    -- Package radius with padding
    r = packed.radius + 10.0
  in
    { id: pkg.id
    , x
    , y
    , vx: 0.0
    , vy: 0.0
    , fx: Nullable.null
    , fy: Nullable.null
    , name: pkg.name
    , source: pkg.source
    , moduleCount: pkg.moduleCount
    , r
    , modules: packedModules
    }
  where
  toModuleCircle :: APIModule -> Circle -> ModuleCircle
  toModuleCircle (APIModule m) c = { id: m.id, name: m.name, x: c.x, y: c.y, r: c.r }

-- | Prepare all packages with circle packing
preparePackages :: Array APIPackage -> Array APIModule -> Array PackageNode
preparePackages packages modules =
  let
    modulesByPkg = groupModulesByPackage modules

    -- Filter to packages with modules, sorted by module count
    packagesWithModules = packages
      # Array.filter (\(APIPackage p) -> p.moduleCount > 0)
      # Array.sortBy (\(APIPackage a) (APIPackage b) -> compare b.moduleCount a.moduleCount)
      # Array.take 40  -- Limit for performance
  in
    packagesWithModules # Array.mapWithIndex \idx pkg@(APIPackage p) ->
      let pkgModules = fromMaybe [] $ Map.lookup p.id modulesByPkg
      in createPackedPackage idx pkg pkgModules

-- =============================================================================
-- Force Simulation
-- =============================================================================

-- | Start the force simulation
-- | Note: Rendering is handled externally - this just runs the physics
startSimulation :: Array PackageNode -> Effect Unit
startSimulation nodes = do
  { handle, events } <- runSimulation
    { engine: D3
    , setup: setup "circle-pack"
        [ manyBody "charge" # withStrength (static (-30.0))
        , collide "collision" # withRadius (dynamic \n -> n.r + 5.0)
        , center "center" # withX (static 0.0) # withY (static 0.0)
        ]
    , nodes: nodes
    , links: []
    , container: "#packages-group"
    , alphaMin: 0.001
    }

  -- Subscribe to events
  _ <- subscribe events \event -> case event of
    Tick _ -> do
      -- In real usage, render nodes here using HATS
      -- currentNodes <- handle.getNodes
      -- renderNodes currentNodes
      pure unit
    Completed -> do
      log "[CirclePackDemo] Simulation converged"
      -- Log final positions
      finalNodes <- handle.getNodes
      log $ "[CirclePackDemo] Final node positions: " <> show (Array.length finalNodes) <> " nodes"
    Started -> log "[CirclePackDemo] Simulation started"
    _ -> pure unit

  pure unit

-- =============================================================================
-- Main Entry Point
-- =============================================================================

main :: Effect Unit
main = launchAff_ do
  log "[CirclePackDemo] Starting..."

  -- Fetch data from API
  log "[CirclePackDemo] Fetching packages..."
  packagesResult <- fetchPackages

  log "[CirclePackDemo] Fetching modules..."
  modulesResult <- fetchModules

  case packagesResult, modulesResult of
    Right packages, Right modules -> do
      log $ "[CirclePackDemo] Loaded " <> show (Array.length packages) <> " packages, "
          <> show (Array.length modules) <> " modules"

      -- Prepare packages with circle packing
      let nodes = preparePackages packages modules
      log $ "[CirclePackDemo] Prepared " <> show (Array.length nodes) <> " package nodes"

      -- Start simulation
      liftEffect $ startSimulation nodes

    Left err, _ -> log $ "[CirclePackDemo] Failed to fetch packages: " <> err
    _, Left err -> log $ "[CirclePackDemo] Failed to fetch modules: " <> err
