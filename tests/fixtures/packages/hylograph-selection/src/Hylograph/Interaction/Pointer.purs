-- | Native Pointer Events based interactions
-- |
-- | This module provides drag and other interactions using the modern
-- | Pointer Events API instead of D3. Benefits:
-- |
-- | - No d3-selection dependency
-- | - Unified mouse/touch/pen support
-- | - Multi-touch capable (via pointerId)
-- | - Better browser integration (setPointerCapture)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Simple drag with callbacks
-- | cleanup <- attachPointerDrag element
-- |   { onStart: \datum x y -> log "Started"
-- |   , onDrag: \datum x y dx dy -> log $ "Moved: " <> show dx
-- |   , onEnd: \datum x y -> log "Ended"
-- |   }
-- |
-- | -- Simulation-aware drag (for force simulations)
-- | cleanup <- attachSimulationDrag element reheatSimulation
-- | ```
module Hylograph.Interaction.Pointer
  ( -- * Drag Behaviors
    attachPointerDrag
  , attachSimulationDrag
  , attachSimulationDragNested
  , PointerDragConfig
    -- * Simple Drag
  , attachSimpleDrag
    -- * Registry-based Drag (for TreeAPI behaviors)
  , registerSimulationForPointer
  , unregisterSimulationForPointer
  , attachSimulationDragById
  , attachSimulationDragNestedById
    -- * Utilities
  , pointerPosition
  , Point
  ) where

import Prelude

import Effect (Effect)
import Web.DOM.Element (Element)
import Web.PointerEvent.PointerEvent (PointerEvent)

-- | 2D point
type Point = { x :: Number, y :: Number }

-- | Configuration for pointer drag behavior
-- |
-- | All callbacks receive the datum bound to the element via `__data__`.
type PointerDragConfig datum =
  { onStart :: datum -> Number -> Number -> Effect Unit
    -- ^ Called on pointer down. Args: datum, clientX, clientY
  , onDrag :: datum -> Number -> Number -> Number -> Number -> Effect Unit
    -- ^ Called on pointer move while dragging. Args: datum, x, y, dx, dy
  , onEnd :: datum -> Number -> Number -> Effect Unit
    -- ^ Called on pointer up. Args: datum, clientX, clientY
  }

-- | Attach drag behavior using native Pointer Events
-- |
-- | Returns a cleanup function that removes all event listeners.
-- |
-- | Features:
-- | - Uses `setPointerCapture` for smooth dragging even outside element
-- | - Sets `touch-action: none` to prevent browser gestures
-- | - Sets cursor to 'grab' / 'grabbing'
-- | - Prevents native drag for images
-- |
-- | ```purescript
-- | cleanup <- attachPointerDrag circleElement
-- |   { onStart: \node _ _ -> log $ "Dragging node " <> show node.id
-- |   , onDrag: \node x y _ _ -> do
-- |       node.fx = x
-- |       node.fy = y
-- |   , onEnd: \node _ _ -> do
-- |       node.fx = null
-- |       node.fy = null
-- |   }
-- |
-- | -- Later, to remove:
-- | cleanup
-- | ```
attachPointerDrag
  :: forall datum
   . Element
  -> PointerDragConfig datum
  -> Effect (Effect Unit)
attachPointerDrag = attachPointerDrag_

-- | Attach simulation-aware drag using Pointer Events
-- |
-- | Simplified version for force simulation nodes:
-- | - Calls reheat function on drag start
-- | - Sets `fx`/`fy` during drag
-- | - Releases `fx`/`fy` on drag end
-- |
-- | The element's `__data__` must be the simulation node directly.
-- |
-- | ```purescript
-- | cleanup <- attachSimulationDrag circleElement reheatSimulation
-- | ```
attachSimulationDrag
  :: Element
  -> Effect Unit  -- ^ Reheat function
  -> Effect (Effect Unit)
attachSimulationDrag = attachSimulationPointerDrag_

-- | Attach simulation-aware drag for nested datum structure
-- |
-- | Like `attachSimulationDrag` but for when the element's datum
-- | has a `.node` field containing the actual simulation node.
-- |
-- | ```purescript
-- | -- Datum is { node :: SimNode, label :: String, ... }
-- | cleanup <- attachSimulationDragNested groupElement reheatSimulation
-- | ```
attachSimulationDragNested
  :: Element
  -> Effect Unit  -- ^ Reheat function
  -> Effect (Effect Unit)
attachSimulationDragNested = attachSimulationPointerDragNested_

-- | Get pointer position relative to a container element
-- |
-- | Handles SVG coordinate transformation via CTM (Current Transform Matrix).
-- | Replacement for d3-selection's `pointer()` function.
-- |
-- | ```purescript
-- | handlePointerMove event = do
-- |   { x, y } <- pointerPosition event svgElement
-- |   log $ "SVG coords: " <> show x <> ", " <> show y
-- | ```
pointerPosition
  :: PointerEvent
  -> Element  -- ^ Container element (usually SVG)
  -> Effect Point
pointerPosition = pointerPosition_

-- =============================================================================
-- FFI
-- =============================================================================

foreign import attachPointerDrag_
  :: forall datum
   . Element
  -> PointerDragConfig datum
  -> Effect (Effect Unit)

foreign import attachSimulationPointerDrag_
  :: Element
  -> Effect Unit
  -> Effect (Effect Unit)

foreign import attachSimulationPointerDragNested_
  :: Element
  -> Effect Unit
  -> Effect (Effect Unit)

foreign import pointerPosition_
  :: PointerEvent
  -> Element
  -> Effect Point

-- =============================================================================
-- Simple Drag
-- =============================================================================

-- | Attach simple drag behavior using Pointer Events
-- |
-- | Moves element via SVG transform attribute.
-- | No simulation awareness - just basic drag.
attachSimpleDrag
  :: Element
  -> Unit
  -> Effect Element
attachSimpleDrag = attachSimpleDrag_

foreign import attachSimpleDrag_
  :: Element
  -> Unit
  -> Effect Element

-- =============================================================================
-- Registry-based Drag (for TreeAPI behaviors)
-- =============================================================================

-- | Register a simulation with the Pointer module's registry
-- |
-- | This enables `attachSimulationDragById` to look up simulations by ID.
-- | Called automatically when using TreeAPI with SimulationDrag behavior.
registerSimulationForPointer
  :: String        -- ^ Simulation ID
  -> Effect Unit   -- ^ Reheat function
  -> Effect Unit
registerSimulationForPointer = registerSimulationForPointer_

-- | Unregister a simulation from the Pointer module's registry
unregisterSimulationForPointer
  :: String  -- ^ Simulation ID
  -> Effect Unit
unregisterSimulationForPointer = unregisterSimulationForPointer_

-- | Attach simulation drag by looking up simulation ID in registry
-- |
-- | Used by TreeAPI's `SimulationDrag simId` behavior.
-- | Element's `__data__` must be the simulation node directly.
attachSimulationDragById
  :: Element
  -> String  -- ^ Simulation ID
  -> Effect Element
attachSimulationDragById = attachSimulationDragById_

-- | Attach simulation drag for nested datum by looking up simulation ID
-- |
-- | Used by TreeAPI's `SimulationDragNested simId` behavior.
-- | Element's `__data__` must have a `.node` field with the simulation node.
attachSimulationDragNestedById
  :: Element
  -> String  -- ^ Simulation ID
  -> Effect Element
attachSimulationDragNestedById = attachSimulationDragNestedById_

foreign import registerSimulationForPointer_
  :: String
  -> Effect Unit
  -> Effect Unit

foreign import unregisterSimulationForPointer_
  :: String
  -> Effect Unit

foreign import attachSimulationDragById_
  :: Element
  -> String
  -> Effect Element

foreign import attachSimulationDragNestedById_
  :: Element
  -> String
  -> Effect Element
