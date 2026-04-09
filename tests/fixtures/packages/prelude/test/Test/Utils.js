export function throwErr(msg) {
  return function () {
    throw new Error(msg);
  };
}


export function log(msg) {
  return function (a) {
    return function () {
      console.log(msg, a);
    }
  }
}

export function stringify(a){
  return JSON.stringify(a);
}