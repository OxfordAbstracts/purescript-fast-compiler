module XTerm.Parser
  ( Parser
  , registerCsiHandler
  , registerDcsHandler
  , registerEscHandler
  , registerOscHandler
  ) where

import Prelude

import Control.Promise (Promise, fromAff)
import Data.Either (Either(..))
import Data.Maybe (maybe)
import Effect (Effect)
import Effect.Aff (Aff)
import Foreign (Foreign, isArray, unsafeFromForeign, unsafeToForeign)
import Foreign.Object (Object, singleton, insert)
import XTerm.Disposable (Disposable)
import XTerm.Parser.FunctionIdentifier (FunctionIdentifier)

type Args = Array (Either Int (Array Int))


type CsiCallback = Args -> Aff Boolean
type DcsCallback = String -> Args -> Aff Boolean


marshallArgs :: Foreign -> Args
marshallArgs f = readArg <$> unsafeFromForeign f
  where
    readArg :: Foreign -> Either Int (Array Int)
    readArg g = 
      if isArray g
        then Right (unsafeFromForeign <$> unsafeFromForeign g)
        else Left $ unsafeFromForeign g

type ForeignCsiCallback = Foreign -> Effect (Promise Boolean)

makeCsiCallback :: CsiCallback -> ForeignCsiCallback
makeCsiCallback c = \a -> fromAff $ c (marshallArgs a) 

type ForeignDcsCallback = String -> Foreign -> Effect (Promise Boolean)

makeDcsCallback :: DcsCallback -> ForeignDcsCallback
makeDcsCallback c s = \a -> fromAff $ c s (marshallArgs a) 

type EscCallback = Aff Boolean

type ForeignEscCallback = Effect (Promise Boolean)

type OscCallback = String -> Aff Boolean

makeOscCallback :: OscCallback -> ForeignOscCallback
makeOscCallback c = \s -> fromAff $ c s

type ForeignOscCallback = String -> Effect (Promise Boolean)

data Parser

foreign import _registerCsiHandler :: Parser -> Foreign -> ForeignCsiCallback -> Effect Disposable

registerCsiHandler :: Parser -> FunctionIdentifier -> CsiCallback -> Effect Disposable
registerCsiHandler p i c = _registerCsiHandler p (makeFunctionIdentifier i) (makeCsiCallback c)

foreign import _registerDcsHandler :: Parser -> Foreign -> ForeignDcsCallback -> Effect Disposable

registerDcsHandler :: Parser -> FunctionIdentifier -> DcsCallback -> Effect Disposable
registerDcsHandler p i c = _registerDcsHandler p (makeFunctionIdentifier i) (makeDcsCallback c)

foreign import _registerEscHandler :: Parser -> Foreign -> ForeignEscCallback -> Effect Disposable

registerEscHandler :: Parser -> FunctionIdentifier -> EscCallback -> Effect Disposable
registerEscHandler p i c = _registerEscHandler p (makeFunctionIdentifier i) (fromAff c)

foreign import _registerOscHandler :: Parser -> Int -> ForeignOscCallback -> Effect Disposable

registerOscHandler :: Parser -> Int -> OscCallback -> Effect Disposable
registerOscHandler p i c = _registerOscHandler p i (makeOscCallback c)


makeFunctionIdentifier :: FunctionIdentifier -> Foreign
makeFunctionIdentifier { prefix, intermediates, final } =
  let o :: Object String
      o = p (i (singleton "final" final)) 
      i = maybe identity (insert "intermediates") intermediates
      p = maybe identity (insert "prefix") prefix
    in unsafeToForeign o

