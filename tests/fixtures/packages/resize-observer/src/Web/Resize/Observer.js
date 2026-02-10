
export const _newResizeObserver = callback => () => {
  const uncurried = (a,o) => {
    callback(a)(o)();
  };
  return new ResizeObserver(uncurried);
};

export const observe = resizeObserver => element => () => {
  resizeObserver.observe(element);
}

export const observeBorderBox = resizeObserver => element => () => {
  resizeObserver.observe(element, { box: "border-box"});
}

export const unobserve = resizeObserver => element => () => {
  resizeObserver.unobserve(element);
}


