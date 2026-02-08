import { Level } from 'level';

const opts = {
    keyEncoding: 'json',
    valueEncoding: 'json'
  };


export const openJson = db_path => () => {
  return new Level(db_path,opts);
}

export const sublevelJson = db => path => () => {
  return db.sublevel(path,opts);
}

export const closeJson = db => () => {
  return db.close();
}




