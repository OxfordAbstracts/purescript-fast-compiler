// WASM Force Engine FFI
// Bridges PureScript to the Rust/WASM force simulation kernel

let wasmModule = null;
let WasmSimulation = null;

// Initialize WASM module (call once at startup)
// EffectFnAff expects (onError, onSuccess) callbacks
export function initWasm_(wasmUrl) {
  return function(onError, onSuccess) {
    (async function() {
      if (wasmModule) {
        console.log('WASM already initialized');
        return;
      }
      // Dynamic import of the WASM module
      const wasm = await import(wasmUrl);
      await wasm.default(); // Initialize WASM
      wasmModule = wasm;
      WasmSimulation = wasm.Simulation;
      console.log('WASM Force Engine initialized');
    })().then(
      // Success handler - EffectFnAff callbacks handle the thunk internally
      () => { onSuccess(); },
      // Error handler - only for actual WASM load failures
      (err) => { onError(err); }
    );

    // Return canceler function (can't really cancel dynamic import)
    return function(cancelError, onCancelError, onCancelSuccess) {
      onCancelSuccess();
    };
  };
}

// Check if WASM is initialized
export function isWasmReady_() {
  return wasmModule !== null;
}

// Create a new WASM simulation
export function createSimulation_(nodeCount) {
  return function() {
    if (!WasmSimulation) {
      throw new Error('WASM not initialized. Call initWasm first.');
    }
    return new WasmSimulation(nodeCount);
  };
}

// Free WASM simulation memory
export function freeSimulation_(sim) {
  return function() {
    if (sim && sim.free) {
      sim.free();
    }
  };
}

// Set node count (resizes internal arrays)
export function setNodeCount_(sim) {
  return function(count) {
    return function() {
      sim.set_node_count(count);
    };
  };
}

// Set links from flat array [source0, target0, source1, target1, ...]
export function setLinks_(sim) {
  return function(links) {
    return function() {
      sim.set_links(new Uint32Array(links));
    };
  };
}

// Set a single node's position
export function setPosition_(sim) {
  return function(index) {
    return function(x) {
      return function(y) {
        return function() {
          sim.set_position(index, x, y);
        };
      };
    };
  };
}

// Set all positions from flat array [x0, y0, x1, y1, ...]
export function setAllPositions_(sim) {
  return function(positions) {
    return function() {
      const nodeCount = sim.node_count();
      for (let i = 0; i < nodeCount && i * 2 + 1 < positions.length; i++) {
        sim.set_position(i, positions[i * 2], positions[i * 2 + 1]);
      }
    };
  };
}

// Get all positions as flat array
export function getPositions_(sim) {
  return function() {
    return Array.from(sim.get_positions());
  };
}

// Get positions as array of {x, y} objects
export function getPositionsAsObjects_(sim) {
  return function() {
    const positions = sim.get_positions();
    const result = [];
    const nodeCount = sim.node_count();
    for (let i = 0; i < nodeCount; i++) {
      result.push({
        x: positions[i * 2],
        y: positions[i * 2 + 1]
      });
    }
    return result;
  };
}

// Fix a node at a position (like D3's fx/fy)
export function fixNode_(sim) {
  return function(index) {
    return function(x) {
      return function(y) {
        return function() {
          sim.fix_node(index, x, y);
        };
      };
    };
  };
}

// Unfix a node
export function unfixNode_(sim) {
  return function(index) {
    return function() {
      sim.unfix_node(index);
    };
  };
}

// Configure many-body force
export function configureManyBody_(sim) {
  return function(config) {
    return function() {
      sim.configure_many_body(
        config.strength,
        config.theta,
        config.distanceMin,
        config.distanceMax
      );
    };
  };
}

// Configure link force
export function configureLinks_(sim) {
  return function(config) {
    return function() {
      sim.configure_links(
        config.distance,
        config.strength,
        config.iterations
      );
    };
  };
}

// Configure center force
export function configureCenter_(sim) {
  return function(config) {
    return function() {
      sim.configure_center(config.x, config.y, config.strength);
    };
  };
}

// Enable/disable forces
export function enableForces_(sim) {
  return function(manyBody) {
    return function(links) {
      return function(center) {
        return function() {
          sim.enable_force(manyBody, links, center);
        };
      };
    };
  };
}

// Set alpha (temperature)
export function setAlpha_(sim) {
  return function(alpha) {
    return function() {
      sim.set_alpha(alpha);
    };
  };
}

// Get current alpha
export function getAlpha_(sim) {
  return function() {
    return sim.get_alpha();
  };
}

// Set alpha decay rate
export function setAlphaDecay_(sim) {
  return function(decay) {
    return function() {
      sim.set_alpha_decay(decay);
    };
  };
}

// Set velocity decay (friction)
export function setVelocityDecay_(sim) {
  return function(decay) {
    return function() {
      sim.set_velocity_decay(decay);
    };
  };
}

// Reheat simulation (reset alpha to 1.0)
export function reheat_(sim) {
  return function() {
    sim.reheat();
  };
}

// Run a single simulation tick, returns new alpha
export function tick_(sim) {
  return function() {
    return sim.tick();
  };
}

// Run multiple ticks
export function tickN_(sim) {
  return function(n) {
    return function() {
      return sim.tick_n(n);
    };
  };
}

// Check if simulation is still running (alpha >= alphaMin)
export function isRunning_(sim) {
  return function() {
    return sim.is_running();
  };
}

// Get node count
export function nodeCount_(sim) {
  return function() {
    return sim.node_count();
  };
}

// Get link count
export function linkCount_(sim) {
  return function() {
    return sim.link_count();
  };
}

// Copy positions from PureScript node array to WASM
export function syncPositionsToWasm_(sim) {
  return function(nodes) {
    return function() {
      for (let i = 0; i < nodes.length; i++) {
        const node = nodes[i];
        sim.set_position(i, node.x, node.y);
      }
    };
  };
}

// Copy positions from WASM back to PureScript node array (mutates nodes!)
export function syncPositionsFromWasm_(sim) {
  return function(nodes) {
    return function() {
      const positions = sim.get_positions();
      for (let i = 0; i < nodes.length; i++) {
        nodes[i].x = positions[i * 2];
        nodes[i].y = positions[i * 2 + 1];
        // Also zero velocities in PureScript (WASM manages its own)
        nodes[i].vx = 0;
        nodes[i].vy = 0;
      }
      return nodes;
    };
  };
}
