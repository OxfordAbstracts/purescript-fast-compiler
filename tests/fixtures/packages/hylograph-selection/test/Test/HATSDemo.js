// HATSDemo FFI - array helpers

export const unsafeIndex = arr => i => arr[i];
export const unsafeSlice = start => end => arr => arr.slice(start, end);
export const length = arr => arr.length;

// GUP demo button setup
export const setupGUPButtons = addHandler => removeHandler => shuffleHandler => () => {
  const addBtn = document.getElementById('gup-add');
  const removeBtn = document.getElementById('gup-remove');
  const shuffleBtn = document.getElementById('gup-shuffle');

  if (addBtn) {
    addBtn.addEventListener('click', () => addHandler()());
  }
  if (removeBtn) {
    removeBtn.addEventListener('click', () => removeHandler()());
  }
  if (shuffleBtn) {
    shuffleBtn.addEventListener('click', () => shuffleHandler()());
  }
};

// Start force simulation using D3 directly
export const startForceSimulation = () => {
  // Get the circles rendered by HATS
  const circles = document.querySelectorAll('.force-node');
  if (circles.length === 0) {
    console.log('No force nodes found');
    return;
  }

  // Create node data with positions from DOM
  const nodes = Array.from(circles).map((el, i) => ({
    id: i,
    x: parseFloat(el.getAttribute('cx')),
    y: parseFloat(el.getAttribute('cy')),
    element: el
  }));

  // Create forces using d3-force (available globally from d3)
  const simulation = d3.forceSimulation(nodes)
    .force('charge', d3.forceManyBody().strength(-80))
    .force('center', d3.forceCenter(150, 75))
    .force('collision', d3.forceCollide().radius(20))
    .alphaDecay(0.02);

  // Update DOM on each tick
  simulation.on('tick', () => {
    nodes.forEach(node => {
      node.element.setAttribute('cx', node.x);
      node.element.setAttribute('cy', node.y);
    });
  });

  simulation.on('end', () => {
    console.log('Force simulation complete');
  });
};
