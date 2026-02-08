import { Level } from 'level';

const opts = {
    keyEncoding: 'json',
    valueEncoding: 'json'
  };

export const putJson = db => key => value => () => {
  return db.put(key,value);
}

export const getJson = db => key => () => {
  const p = new Promise((resolve,reject) => {
    const callback = (err,res) => {
        resolve(res);
    };
    db.get(key,opts,callback);
  });
  return p;
}

export const batchJson = db => ops => () => {
  const p = new Promise((resolve,reject) => {
    const callback = (err,res) => {
        resolve(res);
    };
    db.batch(ops,opts,callback);
  });
  return p;
}


export const getManyJson = db => keys => () => {
  const p = new Promise((resolve,reject) => {
    const callback = (err,res) => {
        resolve(res);
    };
    db.getMany(keys,opts,callback);
  });
  return p;
}

export const delJson = db => key => () => {
  return db.del(key);
}

export const allJson = db => () => {
  return db.iterator().all();
};


export const allKeysJson = db => () => {
  return db.keys().all();
};

export const nextEntryUpJson = db => k => () => {
  return db.iterator({ gt: k, limit: 1 }).all();
};

export const nextEntryDnJson = db => k => () => {
  return db.iterator({ lt: k, limit: 1, reverse: true }).all();
};


export const onPutJson = db => f => () => {
  db.on('put', function(key, value) {
    f(key)(value)();
  });
}
