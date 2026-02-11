module Graphics.CanvasAction.Run where

import Prelude

import Control.Monad.Reader (asks, runReaderT)
import Data.Symbol (class IsSymbol)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class as Aff
import Effect.Class as Effect
import Graphics.Canvas (Context2D)
import Graphics.CanvasAction.Types (CanvasAction, CanvasAff)
import Prim.Row as Row
import Run (AFF, EFFECT, Run, case_, lift, on, runRec)
import Run.Reader (Reader(..), askAt, runReaderAt)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

type CTX r = (ctx ∷ Reader Context2D | r)

-- | Proxy for `"ctx"`
_ctx ∷ Proxy "ctx"
_ctx = Proxy

-- | Runs a `CTX` reader effect.
runCtx ∷ ∀ r. Context2D → Run (CTX + r) ~> Run r
runCtx = runReaderAt _ctx

-- | Lift a `CanvasAction` into `Run` via the `ctx` and `effect` labels
liftCanvasAction ∷ ∀ r. CanvasAction ~> Run (CTX + EFFECT + r)
liftCanvasAction = liftCanvasActionAt _ctx (Proxy ∷ _ "effect")

-- | Lift a `CanvasAction` into `Run` via the provided labels
liftCanvasActionAt
  ∷ ∀ ctx effect ra rb r
  . IsSymbol ctx
  ⇒ IsSymbol effect
  ⇒ Row.Cons ctx (Reader Context2D) ra r
  ⇒ Row.Cons effect Effect rb r
  ⇒ Proxy ctx
  → Proxy effect
  → CanvasAction ~> Run r
liftCanvasActionAt ctxSym effectSym m = do
  ctx ← askAt ctxSym
  lift effectSym (runReaderT m ctx)

-- | Runs `CTX` and `EFFECT` effects in `CanvasAction`
runBaseCanvas ∷ Run (CTX + EFFECT + ()) ~> CanvasAction
runBaseCanvas = runBaseCanvasAt _ctx (Proxy ∷ _ "effect")

-- | Runs `Reader Context2D` and `Effect` in `CanvasAction` at the provided
-- | labels
runBaseCanvasAt
  ∷ ∀ ctx effect r1 r2
  . IsSymbol ctx
  ⇒ IsSymbol effect
  ⇒ Row.Cons ctx (Reader Context2D) () r1
  ⇒ Row.Cons effect Effect r1 r2
  ⇒ Proxy ctx
  → Proxy effect
  → Run r2 ~> CanvasAction
runBaseCanvasAt ctxSym effectSym = case_
  # on ctxSym (\(Reader f) → asks f)
  # on effectSym Effect.liftEffect
  # runRec

-- | Lift a `CanvasAff` into `Run` via the `ctx` and `aff` labels
liftCanvasAff ∷ ∀ r. CanvasAff ~> Run (CTX + AFF + r)
liftCanvasAff = liftCanvasAffAt _ctx (Proxy ∷ _ "aff")

-- | Lift a `CanvasAff` into `Run` via the provided labels
liftCanvasAffAt
  ∷ ∀ ctx aff ra rb r
  . IsSymbol ctx
  ⇒ IsSymbol aff
  ⇒ Row.Cons ctx (Reader Context2D) ra r
  ⇒ Row.Cons aff Aff rb r
  ⇒ Proxy ctx
  → Proxy aff
  → CanvasAff ~> Run r
liftCanvasAffAt ctxSym affSym m = do
  ctx ← askAt ctxSym
  lift affSym (runReaderT m ctx)

-- | Runs `CTX` and `AFF` effects in `CanvasAff`
runBaseCanvasAff ∷ Run (CTX + AFF + ()) ~> CanvasAff
runBaseCanvasAff = runBaseCanvasAffAt _ctx (Proxy ∷ _ "aff")

-- | Runs `Reader Context2D` and `Aff` in `CanvasAff` at the provided labels
runBaseCanvasAffAt
  ∷ ∀ ctx aff r1 r2
  . IsSymbol ctx
  ⇒ IsSymbol aff
  ⇒ Row.Cons ctx (Reader Context2D) () r1
  ⇒ Row.Cons aff Aff r1 r2
  ⇒ Proxy ctx
  → Proxy aff
  → Run r2 ~> CanvasAff
runBaseCanvasAffAt ctxSym affSym = case_
  # on ctxSym (\(Reader f) → asks f)
  # on affSym Aff.liftAff
  # runRec

-- | Runs `CTX`, `EFFECT`, and `AFF` effects in `CanvasAff`
runBaseCanvasAff' ∷ Run (CTX + EFFECT + AFF + ()) ~> CanvasAff
runBaseCanvasAff' =
  runBaseCanvasAffAt' _ctx (Proxy ∷ _ "effect") (Proxy ∷ _ "aff")

-- | Runs `Reader Context2D`, `Effect`, and `Aff` in `CanvasAff` at the provided
-- | labels
runBaseCanvasAffAt'
  ∷ ∀ ctx effect aff r1 r2 r3
  . IsSymbol ctx
  ⇒ IsSymbol effect
  ⇒ IsSymbol aff
  ⇒ Row.Cons ctx (Reader Context2D) () r1
  ⇒ Row.Cons effect Effect r1 r2
  ⇒ Row.Cons aff Aff r2 r3
  ⇒ Proxy ctx
  → Proxy effect
  → Proxy aff
  → Run r3 ~> CanvasAff
runBaseCanvasAffAt' ctxSym effectSym affSym = case_
  # on ctxSym (\(Reader f) → asks f)
  # on effectSym Effect.liftEffect
  # on affSym Aff.liftAff
  # runRec
