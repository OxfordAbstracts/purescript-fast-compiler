import * as go from 'gojs';

export const setUnsafe = (g) => (fields) => () => {
  for (attr in fields) {
      let innit = g;
      let attrChain = attr.split(".");
      let last = attrChain.pop()
      for (i in attrChain) {
          innit = innit[attrChain[i]]
      }
      innit[last] = fields[attr]
  }
}

export const unsafeRecUnion = (r1) => (r2) => {
  var copy = {};
  for (var k1 in r2) {
    if ({}.hasOwnProperty.call(r2, k1)) {
      // r2[k1] is a record, so this should be recursively called
      copy[k1] = r2[k1];
    }
  }
}