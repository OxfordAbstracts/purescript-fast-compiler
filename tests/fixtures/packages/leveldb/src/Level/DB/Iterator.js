import { Level } from 'level';


export const iteratorJson = db => opts => () => {
  return db.iterator(opts);
};

export const nextJson = iter => () => {
  return iter.next();
};

export const closeIteratorImpl = iter => () => {
  return iter.close();
};
