// Test FFI for DOM manipulation

export const getElementById = function(id) {
  return function() {
    const el = document.getElementById(id);
    if (!el) {
      console.error("Element not found:", id);
    }
    return el;
  };
};

export const setStyle = function(element) {
  return function(property) {
    return function(value) {
      return function() {
        if (element) {
          element.style[property] = value;
        }
      };
    };
  };
};

export const setTransform = function(element) {
  return function(value) {
    return function() {
      if (element) {
        element.style.transform = value;
      }
    };
  };
};

export const setPosition = function(element) {
  return function(x) {
    return function(y) {
      return function() {
        if (element) {
          element.style.left = x + "px";
          element.style.top = y + "px";
        }
      };
    };
  };
};

export const logValue = function(label) {
  return function(value) {
    return function() {
      console.log(label + ":", value.toFixed(3));
    };
  };
};
