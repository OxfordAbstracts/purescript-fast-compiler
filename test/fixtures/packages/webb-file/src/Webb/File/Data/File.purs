module Webb.File.Data.File where

import Prelude

import Data.Lens (Lens', over, set)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (class Newtype, unwrap, wrap)
import Effect (Effect)
import Node.FS (FileDescriptor)
import Type.Proxy (Proxy(..))
import Webb.Directory.Data.Absolute (AbsolutePath, AbsPath)
import Webb.Random as Random


{- Maintain state of the File. -}

newtype File = F File_

instance Eq File where
  eq a b = id a == id b

derive instance Newtype File _
instance Show File where
  show (F s) = show 
    { path: s.path
    , id: s.id
    , position: s.position
    , appending: s.appending
    , fd: const unit <$> s.fd
    }

type File_ = 
  { path :: AbsolutePath
  , fd :: Maybe Fd
  , id :: String
  , position :: Int
  , appending :: Boolean
  }

_path :: forall a r. Lens' { path :: a | r } a
_path = prop (Proxy :: Proxy "path")

_fd :: forall a r. Lens' { fd :: a | r } a
_fd = prop (Proxy :: Proxy "fd")

_id :: forall a r. Lens' { id :: a | r } a
_id = prop (Proxy :: Proxy "id")

_position :: forall a r. Lens' { position :: a | r } a
_position = prop (Proxy :: Proxy "position")

_appending :: forall a r. Lens' { appending :: a | r } a
_appending = prop (Proxy :: Proxy "appending")
  

type Fd = FileDescriptor

emptyFile :: AbsPath -> Effect File
emptyFile path' = do
  id' <- Random.randomId
  pure $ wrap { path: path', id: id', fd: Nothing, position: 0, appending: false }

id :: File -> String
id = unwrap >>> _.id

path :: File -> AbsPath
path = unwrap >>> _.path

position :: File -> Int
position = unwrap >>> _.position

isAppending :: File -> Boolean
isAppending = unwrap >>> _.appending

appending :: Boolean -> File -> File
appending flag = unwrap >>> set _appending flag >>> wrap

updatePosition :: (Int -> Int) -> File -> File
updatePosition f = unwrap >>> over _position f >>> wrap

setPosition :: Int -> File -> File
setPosition n = updatePosition (const n)

fd :: File -> Maybe Fd
fd = unwrap >>> _.fd

isOpen :: File -> Boolean
isOpen = unwrap >>> _.fd >>> isJust

isClosed :: File -> Boolean
isClosed = isOpen >>> not

loadFd :: Fd -> File -> File
loadFd fd' = unwrap >>> set _fd (Just fd') >>> wrap

unloadFd :: File -> File
unloadFd = unwrap >>> set _fd Nothing >>> wrap