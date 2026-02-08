module XTerm.Buffer.Namespace where

import Data.Unit (Unit)
import Effect (Effect)
import XTerm.Buffer (Buffer)
import XTerm.Disposable (Disposable)

data BufferNamespace

foreign import active :: BufferNamespace -> Buffer
foreign import normal :: BufferNamespace -> Buffer
foreign import alternate :: BufferNamespace -> Buffer
foreign import onBufferChange :: BufferNamespace -> (Buffer -> Effect Unit) -> Effect Disposable

