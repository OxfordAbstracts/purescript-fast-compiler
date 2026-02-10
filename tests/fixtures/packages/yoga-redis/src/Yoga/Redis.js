import Redis from 'ioredis';

// Create Redis client
export const createRedisImpl = (config) => new Redis(config);

// Connection
export const connectImpl = (redis) => redis.connect();

export const disconnectImpl = (redis) => Promise.resolve(redis.disconnect());

export const quitImpl = (redis) => redis.quit();

export const pingImpl = (redis) => redis.ping();

// String Operations
export const getImpl = (redis, key) => redis.get(key);

export const setImpl = (redis, key, value, opts) => {
  const args = [key, value];
  
  if (opts.ex !== undefined) {
    args.push('EX', opts.ex);
  }
  if (opts.px !== undefined) {
    args.push('PX', opts.px);
  }
  if (opts.nx === true) {
    args.push('NX');
  }
  if (opts.xx === true) {
    args.push('XX');
  }
  if (opts.keepttl === true) {
    args.push('KEEPTTL');
  }
  
  return redis.set(...args);
};

export const setexImpl = (redis, key, seconds, value) => 
  redis.setex(key, seconds, value);

export const delImpl = (redis, keys) => redis.del(...keys);

export const existsImpl = (redis, keys) => redis.exists(...keys);

export const expireImpl = (redis, key, seconds) => 
  redis.expire(key, seconds).then(result => result === 1);

export const ttlImpl = (redis, key) => redis.ttl(key);

export const incrImpl = (redis, key) => redis.incr(key);

export const incrByImpl = (redis, key, increment) => redis.incrby(key, increment);

export const decrImpl = (redis, key) => redis.decr(key);

export const decrByImpl = (redis, key, decrement) => redis.decrby(key, decrement);

// Hash Operations
export const hgetImpl = (redis, key, field) => redis.hget(key, field);

export const hsetImpl = (redis, key, fieldValues) => {
  const args = [key];
  for (const fv of fieldValues) {
    args.push(fv.field, fv.value);
  }
  return redis.hset(...args);
};

export const hgetallImpl = async (redis, key) => {
  const obj = await redis.hgetall(key);
  return Object.entries(obj).map(([field, value]) => ({ field, value }));
};

export const hdelImpl = (redis, key, fields) => redis.hdel(key, ...fields);

export const hexistsImpl = (redis, key, field) => 
  redis.hexists(key, field).then(result => result === 1);

export const hkeysImpl = (redis, key) => redis.hkeys(key);

export const hlenImpl = (redis, key) => redis.hlen(key);

// List Operations
export const lpushImpl = (redis, key, values) => redis.lpush(key, ...values);

export const rpushImpl = (redis, key, values) => redis.rpush(key, ...values);

export const lpopImpl = (redis, key) => redis.lpop(key);

export const rpopImpl = (redis, key) => redis.rpop(key);

export const lrangeImpl = (redis, key, start, stop) => redis.lrange(key, start, stop);

export const llenImpl = (redis, key) => redis.llen(key);

// Set Operations
export const saddImpl = (redis, key, members) => redis.sadd(key, ...members);

export const sremImpl = (redis, key, members) => redis.srem(key, ...members);

export const smembersImpl = (redis, key) => redis.smembers(key);

export const sismemberImpl = (redis, key, member) => 
  redis.sismember(key, member).then(result => result === 1);

export const scardImpl = (redis, key) => redis.scard(key);

// Sorted Set Operations
export const zaddImpl = (redis, key, members, opts) => {
  const args = [key];
  
  if (opts.nx === true) {
    args.push('NX');
  }
  if (opts.xx === true) {
    args.push('XX');
  }
  if (opts.gt === true) {
    args.push('GT');
  }
  if (opts.lt === true) {
    args.push('LT');
  }
  if (opts.ch === true) {
    args.push('CH');
  }
  
  for (const member of members) {
    args.push(member.score, member.value);
  }
  
  return redis.zadd(...args);
};

export const zremImpl = (redis, key, members) => redis.zrem(key, ...members);

export const zrangeImpl = async (redis, key, start, stop) => {
  const results = await redis.zrange(key, start, stop, 'WITHSCORES');
  const members = [];
  
  // Results come as [value1, score1, value2, score2, ...]
  for (let i = 0; i < results.length; i += 2) {
    members.push({
      value: results[i],
      score: parseFloat(results[i + 1])
    });
  }
  
  return members;
};

export const zcardImpl = (redis, key) => redis.zcard(key);

export const zscoreImpl = async (redis, key, member) => {
  const score = await redis.zscore(key, member);
  return score !== null ? parseFloat(score) : null;
};

// Pub/Sub Operations
export const publishImpl = (redis, channel, message) => redis.publish(channel, message);
