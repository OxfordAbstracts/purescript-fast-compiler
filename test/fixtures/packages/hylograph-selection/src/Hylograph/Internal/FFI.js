// D3 dependencies: d3-force, d3-shape (arc only), d3-scale-chromatic, d3-scale
// NOTE: d3-selection REMOVED - use native DOM APIs
// NOTE: d3-drag REMOVED - use PSD3.Interaction.Pointer for native drag
// NOTE: d3-zoom REMOVED - use PSD3.Interaction.Zoom for native zoom
// NOTE: d3-chord removed - use DataViz.Layout.Chord from psd3-layout
// NOTE: d3-hierarchy removed - use DataViz.Layout.Hierarchy.Pack from psd3-layout
// NOTE: d3-ease removed - unused (PureScript Transition.Engine handles easing)
// NOTE: d3-shape links (linkHorizontal/Vertical/Radial) removed - Path DSL handles links
import {
  forceSimulation, forceCenter, forceCollide, forceLink,
  forceManyBody, forceRadial, forceX, forceY
} from "d3-force";
import { arc } from "d3-shape";
import { schemeCategory10, schemeTableau10, interpolateRdYlGn, interpolateViridis } from "d3-scale-chromatic";
import { scaleLinear, scaleOrdinal } from "d3-scale";

// =============================================================================
// Direct D3 Re-exports (for demo components to use without direct D3 imports)
// =============================================================================
// NOTE: select/selectAll removed - use native DOM document.querySelector/querySelectorAll
export { schemeCategory10, schemeTableau10, interpolateRdYlGn, interpolateViridis };
export { scaleLinear, scaleOrdinal };

const debug = false

// NOTE: Most d3-selection wrapper functions have been removed.
// Selection operations now use PureScript web-dom libraries directly.
// Drag behaviors now use native Pointer Events via PSD3.Interaction.Pointer.

export function getIndexFromDatum_(datum) { return (typeof datum.index == `undefined`) ? "?" : datum.index }

// DEPRECATED: selectionOn_ - use element.addEventListener() directly
export function selectionOn_(selection) {
  console.warn('[DEPRECATED] selectionOn_ is deprecated. Use element.addEventListener() instead.');
  return event => callback => {
    // For backward compat, try to call .on() if it exists
    if (selection && typeof selection.on === 'function') {
      return selection.on(event, callback);
    }
    console.error('selectionOn_: selection does not have .on() method');
    return selection;
  };
}

// DEPRECATED: d3AddTransition_ - use pure PureScript transitions or Web Animations API
export function d3AddTransition_(selection) {
  console.warn('[DEPRECATED] d3AddTransition_ is deprecated. Use withPureTransitions or Web Animations API.');
  return transition => {
    // For backward compat, try to call .transition() if it exists
    if (selection && typeof selection.transition === 'function') {
      var handle;
      if (transition.name == '') {
        handle = selection.transition();
        if (transition.duration != 0) {
          handle.duration(transition.duration);
        }
        if (transition.delay != 0) {
          handle.delay(transition.delay);
        }
      } else {
        handle = selection.transition(transition.name);
      }
      return handle;
    }
    console.error('d3AddTransition_: selection does not have .transition() method');
    return selection;
  };
}
export const linksForceName_ = "links"
export const dummyForceHandle_ = null
export function disableTick_(simulation) { return name => { return simulation.on('tick.' + name, () => null) } }
export function forceCenter_() { return forceCenter() }
export function forceCollideFn_() { return forceCollide() }
export function forceCustom_(forceFn) { return forceFn() }
export function forceLink_() { return forceLink().id(d => d.id) }
export function forceMany_() { return forceManyBody() }
export function forceRadial_() { return forceRadial() }
export function forceX_() { return forceX() }
export function forceY_() { return forceY() }
export function getLinksFromForce_(linkForce) { return linkForce.links() }
export function getNodes_(simulation) { return simulation.nodes() }
export function keyIsID_(d) {
  // SimulationNode is row-polymorphic - user data fields are at top level
  return d.id;
}
export function keyIsSourceTarget_(d) {
  // console.log(`FFI: looking up the id of node: ${[d.source, d.target]}`);
  return [d.source, d.target];
}

// Key function for swizzled links - extracts id from the node objects
// Uses 'id' field to match link source/target IDs
export function swizzledLinkKey_(d) {
  // After swizzling, source/target are node objects with 'id' field
  const sourceId = typeof d.source === 'object' ? d.source.id : d.source;
  const targetId = typeof d.target === 'object' ? d.target.id : d.target;
  return `${sourceId}->${targetId}`;
}
export function setAlpha_(simulation) {
  return alpha => {
    simulation.alpha(alpha)
  }
}
export function setAlphaDecay_(simulation) { return alphaDecay => simulation.alphaDecay(alphaDecay) }
export function setAlphaMin_(simulation) { return alphaMin => simulation.alphaMin(alphaMin) }
export function setAlphaTarget_(simulation) { return alphaTarget => simulation.alphaTarget(alphaTarget) }
export function setAsNullForceInSimulation_(simulation) { return label => simulation.force(label, null) }
export function setForceCx_(force) { return attr => force.cx(attr) }
export function setForceCy_(force) { return attr => force.cy(attr) }
export function setForceDistance_(force) { return attr => force.distance(attr) }
export function setForceDistanceMax_(force) { return attr => force.distanceMax(attr) }
export function setForceDistanceMin_(force) { return attr => force.distanceMin(attr) }
export function setForceIterations_(force) { return attr => force.iterations(attr) }
export function setForceRadius_(force) { return attr => force.radius(attr) }
export function setForceStrength_(force) { return attr => force.strength(attr) }
export function setForceTheta_(force) { return attr => force.theta(attr) }
export function setForceX_(force) { return attr => force.x(attr) }
export function setForceY_(force) { return attr => force.y(attr) }
export function setLinksKeyFunction_(force) { return attr => force.id(attr) }
export function setVelocityDecay_(simulation) { return velocityDecay => simulation.velocityDecay(velocityDecay) }
export function startSimulation_(simulation) {
  // IMPORTANT: restart() alone doesn't reset alpha - we need to set it to 1.0 first
  simulation.alpha(1.0).restart();
}
export function stopSimulation_(simulation) { return simulation.stop() }
export function initSimulation_(config) {
  return keyFn => {
    const simulation = forceSimulation([])
      .force(linksForceName_, forceLink([]).id(keyFn))
      .alpha(config.alpha) // default is 1
      .alphaTarget(config.alphaTarget) // default is 0
      .alphaMin(config.alphaMin) // default is 0.0001
      .alphaDecay(config.alphaDecay) // default is 0.0228
      .velocityDecay(config.velocityDecay) // default is 0.4
    // Expose simulation to window for force control panel
    window._psd3_simulation = simulation;
    return simulation
  }
}
export function configSimulation_(simulation) {
  return config => {
    simulation
      .alpha(config.alpha) // default is 1
      .alphaTarget(config.alphaTarget) // default is 0
      .alphaMin(config.alphaMin) // default is 0.0001
      .alphaDecay(config.alphaDecay) // default is 0.0228
      .velocityDecay(config.velocityDecay) // default is 0.4
    if (debug) {
      console.log(`FFI: configSimulation${simulation}${config}`)
    }
    return simulation
  }
}
export function readSimulationVariables_(simulation) {
  return {
    alpha: simulation.alpha(),
    alphaTarget: simulation.alphaTarget(),
    alphaMin: simulation.alphaMin(),
    alphaDecay: simulation.alphaDecay(),
    velocityDecay: simulation.velocityDecay()
  }
}

// DEPRECATED: d3PreserveSimulationPositions_ - no longer uses D3 selections
// The selection parameter is now expected to be an array of elements or nodes
export function d3PreserveSimulationPositions_(selectionOrNodes) {
  return nodedata => keyFn => {
    console.warn('[DEPRECATED] d3PreserveSimulationPositions_ is deprecated. Use simulation.nodes() directly.');
    // Try to get data from selection (D3) or assume it's already node data
    let oldData;
    if (selectionOrNodes && typeof selectionOrNodes.data === 'function') {
      oldData = selectionOrNodes.data();
    } else if (Array.isArray(selectionOrNodes)) {
      oldData = selectionOrNodes;
    } else {
      oldData = [];
    }

    const oldNodeMap = new Map(oldData.map(d => [keyFn(d), d]));
    const newNodeMap = new Map(nodedata.map(d => [keyFn(d), d]));

    let updatedNodeData = nodedata.map(d => {
      let id = keyFn(d);
      let newNode = newNodeMap.get(id);
      let shell = {};
      if (newNode) {
        shell = { fx: newNode.fx, fy: newNode.fy, gridXY: newNode.gridXY, updated: true };
      }
      return Object.assign(oldNodeMap.get(id) || d, shell);
    });
    return updatedNodeData;
  };
}

// DEPRECATED: d3PreserveLinkReferences_ - no longer uses D3 selections
export function d3PreserveLinkReferences_(linkSelectionOrData) {
  return links => {
    console.warn('[DEPRECATED] d3PreserveLinkReferences_ is deprecated.');
    let oldData;
    if (linkSelectionOrData && typeof linkSelectionOrData.data === 'function') {
      oldData = linkSelectionOrData.data();
    } else if (Array.isArray(linkSelectionOrData)) {
      oldData = linkSelectionOrData;
    } else {
      oldData = [];
    }

    const old = new Map(oldData.map(d => [getLinkID_(d), d]));
    let updatedLinkData = links.map(d => Object.assign(old.get(getLinkID_(d)) || d, {}));
    return updatedLinkData;
  };
}
export function getIDsFromNodes_(nodes) {
  return keyFn => {
    const keys = [];
    for (let i = 0; i < nodes.length; i++) {
      keys[i] = keyFn(nodes[i]);
    }
    return keys
  }
}

export function setNodes_(simulation) {
  return nodes => {
    // Get old nodes from simulation to preserve their positions
    const oldNodes = simulation.nodes();

    // Create map of old nodes by ID for O(1) lookup
    const oldNodeMap = new Map(oldNodes.map(d => [d.id, d]));

    // Merge positions from old nodes into new nodes
    const nodesWithPositions = nodes.map(newNode => {
      const oldNode = oldNodeMap.get(newNode.id);
      if (oldNode) {
        // Preserve simulation state (position, velocity) from old node
        // But keep any explicitly set fx/fy from new node (for pinning)
        return Object.assign({}, newNode, {
          x: oldNode.x,
          y: oldNode.y,
          vx: oldNode.vx,
          vy: oldNode.vy,
          // Only override fx/fy if new node has them explicitly set
          fx: newNode.fx !== undefined ? newNode.fx : oldNode.fx,
          fy: newNode.fy !== undefined ? newNode.fy : oldNode.fy
        });
      }
      return newNode; // New node, no position to preserve
    });

    simulation.nodes(nodesWithPositions);
    return simulation.nodes();
  }
}
// we're going to always use the same name for the links force denominated by the linksForceName string
export function setLinks_(simulation) {
  return links => {
    const linkForce = simulation.force(linksForceName_);
    if (linkForce) {
      linkForce.links(links);
    }
  }
}
// returns array of links with ids replaced by object references, invalid links are discarded
// Creates copies of links to avoid mutating the original array
export function swizzleLinks_(links) {
  return simNodes => keyFn => {
    const nodeById = new Map(simNodes.map(d => [keyFn(d), d])); // creates a map from our chosen id to the old obj reference

    // Map to copies first, then filter - this prevents mutation of original links
    // Note: Must explicitly copy source/target as they may be on prototype (PureScript records)
    const swizzledLinks = links.map(link => ({
      source: link.source,
      target: link.target,
      ...link
    })).filter((link, index, arr) => {
      // look up both source and target (which could be id or obj reference)
      // if both source and target are found in nodeMap then we can swizzle and return true
      // else we just return false and this node will go in the bit bucket
      if (typeof link.source !== "object") {
        link.source = nodeById.get(link.source) // try to get object reference if we don't have it
      } else {
        link.source = nodeById.get(keyFn(link.source)) // try to replace object reference with new object reference
      }
      if (typeof link.target !== "object") {
        link.target = nodeById.get(link.target)
      } else {
        link.target = nodeById.get(keyFn(link.target))
      }
      // now let's see what we got from that and if we have a valid link or not
      if (typeof link.source === 'undefined' || link.target === 'undefined') {
        return false; // filter this link
      } else {
        link.id = keyFn(link.source) + "-" + keyFn(link.target)
        return true // we've updated the link
      }
    })
    return swizzledLinks
  }
}
export function unsetLinks_(simulation) {
  // Set link force to null - this is now only called when links shouldn't be displayed at all
  // Scenes that need links displayed should keep the link force in their activeForces
  simulation.force(linksForceName_, null)
  return simulation
}
// this will work on both swizzled and unswizzled links
export function getLinkID_(keyFn) {
  return link => { // version for generating an ID for the link object
    const sourceID = (typeof link.source == `object`) ? keyFn(link.source) : link.source
    const targetID = (typeof link.target == `object`) ? keyFn(link.target) : link.target
    return sourceID + "-" + targetID
  }
}
// For unswizzled links, source/target are just the ID values directly
// (swizzled links would have objects, but this function is for filtering unswizzled links)
export function getLinkIDs_(link) {
  return { sourceID: link.source, targetID: link.target }
}
export function getLinksFromSimulation_(simulation) {
  linksForce = simulation.force(linksForceName_)
  if (typeof linksForce === `undefined`) {
    return [] // either the force wasn't found, or the force wasn't a links force
  }
  const result = linksForce.links()
  if (typeof result === `undefined`) {
    return []
  }
  return result
}
export function onTick_(simulation) {
  return name => tickFn => {
    var result = simulation.on('tick.' + name, () => {
      tickFn()
    })
    return result;
  }
}
// DEPRECATED: defaultNodeTick_ - use native DOM tick handlers
// This function expects a D3 selection. Consider using element arrays with native setAttribute.
export function defaultNodeTick_(label) {
  return simulation => nodeSelectionOrElements => {
    console.warn('[DEPRECATED] defaultNodeTick_ is deprecated. Use native DOM tick handlers.');
    simulation.on('tick.' + label, () => {
      // Try D3 selection API first, then fall back to element array
      if (nodeSelectionOrElements && typeof nodeSelectionOrElements.attr === 'function') {
        nodeSelectionOrElements.attr('cx', d => d.x).attr('cy', d => d.y);
      } else if (nodeSelectionOrElements && nodeSelectionOrElements.forEach) {
        nodeSelectionOrElements.forEach(el => {
          const d = el.__data__;
          if (d) {
            el.setAttribute('cx', d.x);
            el.setAttribute('cy', d.y);
          }
        });
      }
    });
  };
}

// DEPRECATED: defaultLinkTick_ - use native DOM tick handlers
// This function expects a D3 selection. Consider using element arrays with native setAttribute.
export function defaultLinkTick_(label) {
  return simulation => linksSelectionOrElements => {
    console.warn('[DEPRECATED] defaultLinkTick_ is deprecated. Use native DOM tick handlers.');
    simulation.on('tick.' + label, () => {
      // Try D3 selection API first, then fall back to element array
      if (linksSelectionOrElements && typeof linksSelectionOrElements.attr === 'function') {
        linksSelectionOrElements
          .attr("x1", d => d.source.x)
          .attr("y1", d => d.source.y)
          .attr("x2", d => d.target.x)
          .attr("y2", d => d.target.y);
      } else if (linksSelectionOrElements && linksSelectionOrElements.forEach) {
        linksSelectionOrElements.forEach(el => {
          const d = el.__data__;
          if (d && d.source && d.target) {
            el.setAttribute('x1', d.source.x);
            el.setAttribute('y1', d.source.y);
            el.setAttribute('x2', d.target.x);
            el.setAttribute('y2', d.target.y);
          }
        });
      }
    });
  };
}
export function lookupForceByName_(simulation) {
  return name => {
    let lookup = simulation.force(name)
    if (typeof lookup === `undefined`) {
      return null;
    }
    return lookup;
  }
}
export function removeFixForceXY_(simulation) {
  return filterFn => {
    let filteredNodes = simulation.nodes().filter(filterFn)
    for (let index = 0; index < filteredNodes.length; index++) {
      // console.log(`removing FixForceXY from node: ${filteredNodes[index].id}`);
      filteredNodes[index].fx = null;
      filteredNodes[index].fy = null;
    }
  }
}
export function removeFixForceX_(simulation) {
  return filterFn => {
    let filteredNodes = simulation.nodes().filter(filterFn)
    for (let index = 0; index < filteredNodes.length; index++) {
      // console.log(`removing FixForceX from node: ${filteredNodes[index].id}`);
      filteredNodes[index].fx = null;
    }
  }
}
export function removeFixForceY_(simulation) {
  return filterFn => {
    let filteredNodes = simulation.nodes().filter(filterFn)
    for (let index = 0; index < filteredNodes.length; index++) {
      // console.log(`removing FixForceY from node: ${filteredNodes[index].id}`);
      filteredNodes[index].fy = null;
    }
  }
}
export function applyFixForceInSimulationXY_(simulation) {
  return label => fn => filterFn => {

    let nodes = simulation.nodes()   // get nodes from simulation
    let filteredNodes = nodes.filter(filterFn)
    for (let index = 0; index < filteredNodes.length; index++) {
      let i = index
      let position = fn(filteredNodes[i])(i)   // set each node's fx,fy using fn function
      filteredNodes[i].fx = position.x
      filteredNodes[i].fy = position.y;
      filteredNodes[i].fixIndex_ = i; // in case _other_ elements need to know the cluster point of this element, because it's index is a filtered index
    }
  }
}
export function applyFixForceInSimulationX_(simulation) {
  return label => fn => filterFn => {
    let nodes = simulation.nodes()
    for (let index = 0; index < nodes.length; index++) {
      if (filterFn(nodes[index])) { // only fix nodes that this thing applies to
        let position = fn(nodes[index])
        nodes[index].fx = position.x
      }
    }
  }
}
export function applyFixForceInSimulationY_(simulation) {
  return label => fn => filterFn => {
    let nodes = simulation.nodes()
    for (let index = 0; index < nodes.length; index++) {
      if (filterFn(nodes[index])) { // only fix nodes that this thing applies to
        let position = fn(nodes[index])
        nodes[index].fy = position.y;
      }
    }
  }
}
export function putForceInSimulation_(simulation) {
  return label => force => {
    // console.log(`FFI: Putting ${label} force in the simulation`);
    simulation.force(label, force)
    // Keep window._psd3_simulation updated for ForceControlPanel
    window._psd3_simulation = simulation;
  }
}

// REVIEW a whole group of side effecting function
export function pinNode_(fx) {
  return fy => node => {
    node.fx = fx
    node.fy = fy
    return node
  }
}
export function pinNamedNode_(name) {
  return fx => fy => node => {
    if (node.name === name) {
      node.fx = fx
      node.fy = fy
    }
    return node
  }
}
export function pinTreeNode_(node) { node.fx = node.treeX; node.fy = node.treeY; return node } // if treeX/Y is null, no harm!
export function setInSimNodeFlag_(node) { node.inSim = true; return node }
export function unsetInSimNodeFlag_(node) { node.inSim = false; return node }
export function unpinNode_(node) { node.fx = null; node.fy = null; return node }
// *****************************************************************************************************************
// ************************** Arc generator from d3-shape (used for pie/donut charts) ******************************
// *****************************************************************************************************************
export function arcGenerator_() { return arc() }
export function arcPath_(generator) { return group => generator(group) }
export function setArcInnerRadius_(generator) { return radius => { generator.innerRadius(radius); return generator } }
export function setArcOuterRadius_(generator) { return radius => { generator.outerRadius(radius); return generator } }
