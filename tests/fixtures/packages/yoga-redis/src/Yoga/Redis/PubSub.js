import Redis from 'ioredis';

// Create subscriber (separate Redis instance for subscriptions)
export const createSubscriberImpl = (config) => new Redis(config);

// Subscribe to channels
export const subscribeImpl = (subscriber, channels, handler) => {
  // Set up message handler
  subscriber.on('message', (channel, message) => {
    handler({
      channel,
      message
    })();
  });
  
  // Subscribe to channels
  return subscriber.subscribe(...channels);
};

// Unsubscribe from channels
export const unsubscribeImpl = (subscriber, channels) => {
  if (channels.length === 0) {
    return subscriber.unsubscribe();
  }
  return subscriber.unsubscribe(...channels);
};

// Pattern subscribe
export const psubscribeImpl = (subscriber, patterns, handler) => {
  // Set up pattern message handler
  subscriber.on('pmessage', (pattern, channel, message) => {
    handler({
      pattern,
      channel,
      message
    })();
  });
  
  // Subscribe to patterns
  return subscriber.psubscribe(...patterns);
};

// Pattern unsubscribe
export const punsubscribeImpl = (subscriber, patterns) => {
  if (patterns.length === 0) {
    return subscriber.punsubscribe();
  }
  return subscriber.punsubscribe(...patterns);
};

// Disconnect subscriber
export const disconnectSubscriberImpl = (subscriber) => subscriber.disconnect();

// Quit subscriber (graceful disconnect)
export const quitSubscriberImpl = (subscriber) => subscriber.quit();
