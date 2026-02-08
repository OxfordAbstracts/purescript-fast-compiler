module TanStack.Query where

import Prelude

import Data.Array (snoc) as Array
import Data.DateTime.Instant (Instant)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable)
import Data.Nullable (toMaybe) as Nullable
import Data.Semigroup.Foldable (intercalateMap)
import Data.Undefined.NoProblem (Opt, pseudoMap)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Console (error) as Console
import Effect.Exception (Error)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, EffectFn4, mkEffectFn1, mkEffectFn2, mkEffectFn4, runEffectFn1, runEffectFn3)
import Foreign (Foreign)
import ForgetMeNot (Id)
import Literals.Undefined (undefined)
import Network.RemoteData (RemoteData(..)) as RD
import Network.RemoteData (RemoteData)
import Partial.Unsafe (unsafeCrashWith)
import Promise (Promise)
import Promise (class Flatten) as Promise
import Promise.Aff (fromAff, toAffE) as Promise
import Prim.Row (class Union)
import React.Basic (JSX, ReactComponent)
import React.Basic.Hooks (bind, element) as React
import React.Basic.Hooks.Internal (Hook, unsafeHook)
import Record (insert) as Record
import Record.Builder (build, modify) as RB
import Type.Prelude (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)
import Yoga.JSON (class ReadForeign, class WriteForeign, unsafeStringify)
import Yoga.JSON (read, write) as JSON
import Yoga.JSON.Error (renderHumanError)

foreign import data UseQuery :: Type -> Type

type UseQueryArgs :: forall k. (Type -> k) -> Type -> Row k
type UseQueryArgs f output =
  ( queryKey :: f QueryKey
  , enabled :: f Boolean
  , queryFn :: f (Aff output)
  )

foreign import useQueryImpl :: forall input output. EffectFn1 input { data :: output, isError :: Boolean, error :: Error, isPending :: Boolean, fetchStatus :: String }

data FetchStatus = Fetching | Paused | Idle

useQuery :: forall opts opts_ @output. Promise.Flatten output output => Union opts opts_ (UseQueryArgs Id output) => { | opts } -> Hook UseQuery { data :: RemoteData Error output, fetchStatus :: FetchStatus }
useQuery args' = React.do
  let
    args :: { | UseQueryArgs Opt output }
    args = unsafeCoerce args'
    argsImpl =
      args # RB.build
        ( RB.modify (Proxy :: Proxy "queryFn")
            (pseudoMap (Promise.fromAff))
        )
  result <- unsafeHook (runEffectFn1 useQueryImpl argsImpl)
  pure
    { data:
        if result.isPending then
          RD.Loading
        else if result.isError then
          RD.Failure result.error
        else RD.Success result.data
    , fetchStatus:
        case result.fetchStatus of
          "fetching" -> Fetching
          "paused" -> Paused
          "idle" -> Idle
          _ -> unsafeCrashWith "Invalid fetchStatus status"
    }

foreign import data UseMutation :: Type -> Type

type UseMutationArgs :: forall k. (Type -> k) -> Type -> Type -> Type -> Row k
type UseMutationArgs f input output ctx =
  ( mutationKey :: f String
  , mutationFn :: f (input -> Aff output)
  , onSettled :: f (Either Error output -> input -> ctx -> Aff Unit)
  , onSuccess :: f (output -> input -> Effect Unit)
  )

type UseMutationImplResult input output =
  { data :: output
  , isIdle :: Boolean
  , isError :: Boolean
  , error :: Error
  , isPending :: Boolean
  , mutateAsync :: EffectFn1 input (Promise Unit)
  , variables :: Nullable input
  , reset :: Effect Unit
  , submittedAt :: Nullable Instant
  }

foreign import useMutationImpl ::
  forall input output ctx.
  EffectFn1
    { mutationFn :: Opt (EffectFn1 input (Promise output))
    , mutationKey :: Opt String
    , onSuccess :: Opt (EffectFn2 output input Unit)
    , onSettled :: Opt (EffectFn4 output (Nullable Error) input ctx (Promise Unit))
    }
    (UseMutationImplResult input output)

type UseMutationResult input output =
  { data :: RemoteData Error output
  , mutateAsync :: input -> Aff Unit
  , variables :: Maybe input
  , reset :: Effect Unit
  , submittedAt :: Maybe Instant
  }

useMutation ::
  forall opts opts_ input @output ctx.
  Promise.Flatten output output =>
  Union opts opts_ (UseMutationArgs Id input output ctx) =>
  { | opts } ->
  Hook UseMutation (UseMutationResult input output)
useMutation args' = React.do
  let
    args :: { | UseMutationArgs Opt input output ctx }
    args = unsafeCoerce args'
    argsImpl =
      args # RB.build
        ( ( RB.modify (Proxy :: Proxy "mutationFn")
              (pseudoMap (\fn -> mkEffectFn1 \i -> Promise.fromAff (fn i)))
          )
            >>>
              ( RB.modify (Proxy :: Proxy "onSuccess")
                  (pseudoMap mkEffectFn2)
              )
            >>>
              ( RB.modify (Proxy :: Proxy "onSettled")
                  ( pseudoMap
                      \fn -> mkEffectFn4 \result err variables ctx -> do
                        let
                          val = case Nullable.toMaybe err of
                            Nothing -> Right result
                            Just e -> Left e
                        Promise.fromAff (fn val variables ctx)
                  )
              )
        )
  implResult :: (UseMutationImplResult input output) <- unsafeHook (runEffectFn1 useMutationImpl argsImpl)
  let

    mutateImpl :: EffectFn1 input (Promise Unit)
    mutateImpl = implResult.mutateAsync

    mutateImplFn :: input -> Effect (Promise Unit)
    mutateImplFn = runEffectFn1 mutateImpl

    mutate :: input -> Aff Unit
    mutate input =
      Promise.toAffE (mutateImplFn input)

    result :: UseMutationResult input output
    result =
      { data:
          if implResult.isIdle then
            RD.NotAsked
          else if implResult.isPending then
            RD.Loading
          else if implResult.isError then
            RD.Failure implResult.error
          else RD.Success implResult.data
      , mutateAsync: mutate
      , reset: implResult.reset
      , variables: Nullable.toMaybe implResult.variables
      , submittedAt: Nullable.toMaybe implResult.submittedAt
      }
  pure result

foreign import queryClientProviderImpl :: forall a. ReactComponent { | a }

queryClientProvider :: { client :: QueryClient } -> (Array JSX) -> JSX
queryClientProvider props children =
  React.element queryClientProviderImpl (props # Record.insert (Proxy :: Proxy "children") children)

foreign import data QueryClient :: Type

foreign import newQueryClient :: Effect QueryClient

foreign import useQueryClientImpl :: Effect QueryClient

foreign import data UseQueryClient :: Type -> Type

useQueryClient :: Hook UseQueryClient QueryClient
useQueryClient = unsafeHook useQueryClientImpl

foreign import invalidateQueries :: { queryKey :: QueryKey } -> QueryClient -> Effect Unit

invalidateAllQueries :: QueryClient -> Effect Unit
invalidateAllQueries = invalidateQueries (unsafeCoerce undefined)

foreign import data QueryKey :: Type

unsafeToQueryKey :: Array Foreign -> QueryKey
unsafeToQueryKey = unsafeCoerce

queryKey :: forall a. WriteForeign a => a -> QueryKey
queryKey x = unsafeToQueryKey [ JSON.write x ]

startQueryKey :: forall a b. WriteForeign a => WriteForeign b => a -> b -> QueryKey
startQueryKey x y = queryKey x % y

infixl 4 startQueryKey as !%

appendQueryKey :: forall a. WriteForeign a => QueryKey -> a -> QueryKey
appendQueryKey qk segment = unsafeToQueryKey (Array.snoc (unsafeCoerce qk) (JSON.write segment))

infixl 4 appendQueryKey as %

foreign import getQueryDataImpl :: QueryKey -> QueryClient -> Effect (Nullable Foreign)

getQueryData :: forall a. ReadForeign a => QueryKey -> QueryClient -> Effect (Maybe a)
getQueryData qk qc = do
  mqd <- getQueryDataImpl qk qc
  case Nullable.toMaybe mqd of
    Nothing -> pure Nothing
    Just qd -> case JSON.read qd of
      Right r -> pure $ Just r
      Left e -> do
        Console.error ("Broken JSON reader for " <> unsafeStringify qk <> ": " <> intercalateMap "\n" renderHumanError e)
        pure Nothing

foreign import setQueryDataImpl :: forall a. EffectFn3 QueryKey a QueryClient Unit

setQueryData :: forall a. WriteForeign a => QueryKey -> a -> QueryClient -> Effect Unit
setQueryData theQueryKey theData queryClient =
  runEffectFn3 setQueryDataImpl theQueryKey (JSON.write theData) queryClient
