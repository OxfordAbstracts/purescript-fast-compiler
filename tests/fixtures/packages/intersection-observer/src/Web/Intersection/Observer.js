
export const _newIntersectionObserver = callback => options => () => {
  const uncurried = (a,o) => {
    callback(a)(o)();
  };
  return new IntersectionObserver(uncurried,options);
};

export const observe = intersectionObserver => element => () => {
  intersectionObserver.observe(element)
}

export const unobserve = intersectionObserver => element => () => {
  intersectionObserver.unobserve(element)
}


