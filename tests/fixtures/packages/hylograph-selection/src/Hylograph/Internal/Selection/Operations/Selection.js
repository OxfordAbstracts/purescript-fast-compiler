// FFI for Selection module

// Get data from an element (D3-style __data__ property)
export const getElementData_ = (element) => () => {
  return element.__data__ !== undefined ? element.__data__ : null;
};
