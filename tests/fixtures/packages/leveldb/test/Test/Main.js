import * as util from 'util';

export const inspect = (o) => {
  return () => {
    console.log(util.inspect(o, {showHidden: false, depth: null, colors: true})); 
  }
}
