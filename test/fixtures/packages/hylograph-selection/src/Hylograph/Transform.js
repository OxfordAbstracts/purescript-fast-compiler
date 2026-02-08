// Generic element transformation based on bound data
//
// Uses native querySelectorAll for performance.
// Reads D3's __data__ property from each element.

// Transform circles: update cx/cy based on bound data
// transformer: (data) -> { cx, cy }
export function transformCircles_(containerSelector) {
  return function(transformer) {
    return function() {
      const selector = containerSelector + " circle";
      const elements = document.querySelectorAll(selector);

      elements.forEach(el => {
        const data = el.__data__;
        if (data !== undefined) {
          const pos = transformer(data);
          el.setAttribute("cx", pos.cx);
          el.setAttribute("cy", pos.cy);
        }
      });
    };
  };
}

// Transform lines: update x1/y1/x2/y2 based on bound data
// transformer: (data) -> { x1, y1, x2, y2 }
export function transformLines_(containerSelector) {
  return function(transformer) {
    return function() {
      const selector = containerSelector + " line";
      const elements = document.querySelectorAll(selector);

      elements.forEach(el => {
        const data = el.__data__;
        if (data !== undefined) {
          const pos = transformer(data);
          el.setAttribute("x1", pos.x1);
          el.setAttribute("y1", pos.y1);
          el.setAttribute("x2", pos.x2);
          el.setAttribute("y2", pos.y2);
        }
      });
    };
  };
}

// Transform paths: update d attribute based on bound data
// transformer: (data) -> pathString
export function transformPaths_(containerSelector) {
  return function(transformer) {
    return function() {
      const selector = containerSelector + " path";
      const elements = document.querySelectorAll(selector);

      elements.forEach(el => {
        const data = el.__data__;
        if (data !== undefined) {
          const d = transformer(data);
          el.setAttribute("d", d);
        }
      });
    };
  };
}

// Transform groups: update transform attribute based on bound data
// transformer: (data) -> "translate(x, y)" or similar transform string
export function transformGroups_(containerSelector) {
  return function(groupSelector) {
    return function(transformer) {
      return function() {
        const selector = containerSelector + " " + groupSelector;
        const elements = document.querySelectorAll(selector);

        elements.forEach(el => {
          const data = el.__data__;
          if (data !== undefined) {
            const transformStr = transformer(data);
            el.setAttribute("transform", transformStr);
          }
        });
      };
    };
  };
}

// Transform groups by ID lookup: update transform using a position lookup function
// lookupFn: (id) -> { x, y } or null
// This variant is useful when positions are computed externally and stored in a Map
export function transformGroupsById_(containerSelector) {
  return function(groupSelector) {
    return function(idAttr) {
      return function(lookupFn) {
        return function() {
          const selector = containerSelector + " " + groupSelector;
          const elements = document.querySelectorAll(selector);

          elements.forEach(el => {
            const id = parseInt(el.getAttribute(idAttr), 10);
            const pos = lookupFn(id);
            if (pos !== null) {
              el.setAttribute("transform", `translate(${pos.x}, ${pos.y})`);
            }
          });
        };
      };
    };
  };
}

// Transform groups by NAME lookup: update transform using a position lookup function
// lookupFn: (name) -> { x, y } or null
// This variant is useful when matching between different data sources by name
export function transformGroupsByName_(containerSelector) {
  return function(groupSelector) {
    return function(nameAttr) {
      return function(lookupFn) {
        return function() {
          const selector = containerSelector + " " + groupSelector;
          const elements = document.querySelectorAll(selector);

          elements.forEach(el => {
            const name = el.getAttribute(nameAttr);
            if (name) {
              const pos = lookupFn(name);
              if (pos !== null) {
                el.setAttribute("transform", `translate(${pos.x}, ${pos.y})`);
              }
            }
          });
        };
      };
    };
  };
}

// Set opacity on groups by ID lookup
// lookupFn: (id) -> opacity (Number) or null
export function setGroupsOpacityById_(containerSelector) {
  return function(groupSelector) {
    return function(idAttr) {
      return function(lookupFn) {
        return function() {
          const selector = containerSelector + " " + groupSelector;
          const elements = document.querySelectorAll(selector);

          elements.forEach(el => {
            const id = parseInt(el.getAttribute(idAttr), 10);
            const opacity = lookupFn(id);
            if (opacity !== null) {
              el.style.opacity = opacity;
            }
          });
        };
      };
    };
  };
}

// Set viewBox on an SVG
export function setViewBox_(containerSelector) {
  return function(minX) {
    return function(minY) {
      return function(width) {
        return function(height) {
          return function() {
            const svg = document.querySelector(containerSelector + " svg");
            if (svg) {
              svg.setAttribute("viewBox", `${minX} ${minY} ${width} ${height}`);
            }
          };
        };
      };
    };
  };
}

// Clear all child elements from a container
export function clearContainer_(selector) {
  return function() {
    const container = document.querySelector(selector);
    if (container) {
      container.innerHTML = "";
    }
  };
}

// Remove an element from the DOM entirely
export function removeElement_(selector) {
  return function() {
    const element = document.querySelector(selector);
    if (element) {
      element.remove();
    }
  };
}
