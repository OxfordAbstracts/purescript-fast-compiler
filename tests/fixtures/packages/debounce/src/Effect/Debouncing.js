import { debounce, throttle } from 'debouncing';


export const debounceImpl = (f) => (interval) => {
  let self = this;
  
  // We need to do this because f is effectful and is wrappd in a function
  return debounce((...args) => { return f.apply(self, args)() }, interval);
}

export const throttleImpl = (f) => (interval) => {
  let self = this;

  // We need to do this because f is effectful and is wrappd in a function
  return throttle((...args) => { return f.apply(self, args)() }, interval);
}

export const callImpl = (d) => (a) => () => {
  d(a);
}
