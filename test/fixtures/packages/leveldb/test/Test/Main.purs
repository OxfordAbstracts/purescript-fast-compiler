module Test.Main where
import Level.DB
import Level.DB.Iterator
import Level.DB.Iterator.Options
import Prelude
import Data.Tuple
import Effect (Effect)
import Effect.Aff (runAff_)
import Effect.Class (liftEffect)
import Data.Options ((:=))
import Control.Monad.Resource (runResourceT)
import Pipes ((>->))
import Pipes.Core (runEffectRec)
import Pipes.Prelude (mapM_)


foreign import inspect :: forall a .  a -> Effect Unit

main :: Effect Unit
main = do
  inspect "testing"
  db  <- open "test/test.db"
  db1 <- sublevel db "string-string"
  onPut db1 $ \k v -> inspect { evt: "eventing!", k: k, v: v }
  db2 <- sublevel db "string-int"
  onPut db2 $ \k v -> inspect { evt: "woop!", k: k, v: v }

  db3 <- sublevel db "time-string"
  onPut db3 $ \k v -> inspect {evt: "num-strang", k, v}

  runAff_ inspect do
    get db1 "helo" >>= (liftEffect <<< inspect)
    get db1 "hello" >>= (liftEffect <<< inspect)
    put db1 "helo" "thar"
    put db1 "hello" "there"
    get db1 "helo" >>= (liftEffect <<< inspect)
    get db1 "hello" >>= (liftEffect <<< inspect)
    del db1 "helo"
    get db1 "helo" >>= (liftEffect <<< inspect)
    get db1 "hello" >>= (liftEffect <<< inspect)
    put db1 "cat" "dog"
    arr <- all db1
    liftEffect $ inspect arr
    getMany db1 ["helo","hello","dog"] >>= (liftEffect <<< inspect)
    putMany db1 [ Tuple "a" "aardvark", Tuple "b" "balls", Tuple "c" "corn", Tuple "d" "ding" ] >>= (liftEffect <<< inspect)
    getMany db1 ["helo","hello","dog","c","d","a","b"] >>= (liftEffect <<< inspect)
    allKeys db1 >>= (liftEffect <<< inspect)
    delMany db1 ["d","dog","a"] >>= (liftEffect <<< inspect)
    getMany db1 ["helo","hello","dog","c","d","a","b"] >>= (liftEffect <<< inspect)

    get db2 "soup" >>= (liftEffect <<< inspect)
    put db2 "soup" 44
    get db2 "soup" >>= (liftEffect <<< inspect)

    let t1 = "2016-04-28T18:22:20.123Z"
        t2 = "2016-04-28T18:23:20.123Z"
        t3 = "2016-04-29T18:22:20.123Z"
        t4 = "2017-04-17T18:22:20.123Z"
        t5 = "2036-04-27T18:22:20.123Z"

    put db3 t1 "1 haberdashery"
    put db3 t2 "2 haberdoshery"
    put db3 t3 "3 hooberdishery"
    put db3 t4 "4 haberdoshery"
    put db3 t5 "5 hooberdishery"

    nextEntryDn db3 t3 >>= (liftEffect <<< inspect)
    nextEntryUp db3 t3 >>= (liftEffect <<< inspect)

    liftEffect $ inspect "iterating"
    it <- liftEffect $ iterator db3 mempty
    next it >>= (liftEffect <<< inspect)
    next it >>= (liftEffect <<< inspect)
    next it >>= (liftEffect <<< inspect)
    next it >>= (liftEffect <<< inspect)
    next it >>= (liftEffect <<< inspect)
    next it >>= (liftEffect <<< inspect)
    closeIterator it

    liftEffect $ inspect "iterating in reverse"
    it <- liftEffect $ iterator db3 (reverse := true)
    next it >>= (liftEffect <<< inspect)
    next it >>= (liftEffect <<< inspect)
    next it >>= (liftEffect <<< inspect)
    next it >>= (liftEffect <<< inspect)
    next it >>= (liftEffect <<< inspect)
    next it >>= (liftEffect <<< inspect)
    closeIterator it

    liftEffect $ inspect "producing"
    runResourceT identity $ runEffectRec ((producer db3 (reverse := true <> lt := t3))
                                           >-> (mapM_ (liftEffect <<< inspect))) 

    close db


