// FFI for WASM Force Simulation
//
// This module provides PureScript bindings to the Rust WASM force kernel.
// The WASM module must be initialized before use.

let wasmModule = null;
let SimulationClass = null;

// Initialize the WASM module (must be called before creating simulations)
// Takes the path to the WASM JS wrapper (e.g., "../showcases/wasm-force-demo/pkg/force_kernel.js")
// Uses EffectFnAff pattern for PureScript Aff compatibility
export const initWasm_ = function(wasmPath) {
  return function(onError, onSuccess) {
    (async () => {
      if (wasmModule) {
        onSuccess();
        return;
      }

      try {
        const module = await import(wasmPath);
        await module.default(); // Call init()
        wasmModule = module;
        SimulationClass = module.Simulation;
        console.log("WASM force kernel initialized");
        onSuccess();
      } catch (e) {
        onError(e);
      }
    })();

    // Return canceler
    return function(cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};

// Check if WASM is initialized
export const isWasmReady = function() {
  return wasmModule !== null;
};

// Create a new WASM simulation with n nodes
export const createSimulation = function(nodeCount) {
  return function() {
    if (!SimulationClass) {
      throw new Error("WASM not initialized. Call initWasm first.");
    }
    return new SimulationClass(nodeCount);
  };
};

// Set initial positions for all nodes
// positions is a flat array [x0, y0, x1, y1, ...]
export const setPositions = function(sim) {
  return function(positions) {
    return function() {
      for (let i = 0; i < positions.length / 2; i++) {
        sim.set_position(i, positions[i * 2], positions[i * 2 + 1]);
      }
    };
  };
};

// Configure many-body force
export const configureManyBody = function(sim) {
  return function(strength) {
    return function(theta) {
      return function(distMin) {
        return function(distMax) {
          return function() {
            sim.configure_many_body(strength, theta, distMin, distMax);
          };
        };
      };
    };
  };
};

// Configure center force
export const configureCenter = function(sim) {
  return function(x) {
    return function(y) {
      return function(strength) {
        return function() {
          sim.configure_center(x, y, strength);
        };
      };
    };
  };
};

// Enable/disable forces
export const enableForces = function(sim) {
  return function(manyBody) {
    return function(links) {
      return function(center) {
        return function() {
          sim.enable_force(manyBody, links, center);
        };
      };
    };
  };
};

// Run one tick, returns alpha
export const tick = function(sim) {
  return function() {
    return sim.tick();
  };
};

// Get current alpha
export const getAlpha = function(sim) {
  return function() {
    return sim.get_alpha();
  };
};

// Check if simulation is still running
export const isRunning = function(sim) {
  return function() {
    return sim.is_running();
  };
};

// Reheat the simulation (set alpha back to 1.0)
export const reheat = function(sim) {
  return function() {
    sim.reheat();
  };
};

// Get all positions as flat Float32Array [x0, y0, x1, y1, ...]
export const getPositions = function(sim) {
  return function() {
    return sim.get_positions();
  };
};

// Get position of a specific node
export const getNodePosition = function(sim) {
  return function(index) {
    return function() {
      const positions = sim.get_positions();
      return { x: positions[index * 2], y: positions[index * 2 + 1] };
    };
  };
};
