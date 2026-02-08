/* We want to return something that is _like_ a promise -- and that in fact 
 * may actually be a promise. And mostly is a promise, lol. To do so, we return
 * a promise, and functions for interacting with it.
*/
export const _result = function() {
  let resolve;
  let reject;

  const promise = new Promise((_resolve, _reject) => {
    resolve = _resolve
    reject = _reject
  })
  
  return {
    promise: promise,
    error: function(e) {
      reject(e)
    },
    set: function(val) {
      resolve(val)
    },
    get: function(onErr, onSuccess) {
      promise.then(val => {
        onSuccess(val)
      }, err => {
        onErr(err)
      })
        
      /* Return a canceler function. For a result, We don't do
       * anything at all -- a cancellation is just a cancellation; nothing
       * needs to be done.
      */
      return function (reasonErr, onCancelErr, onCancelSuccess) {
        /* We don't care about the cancellation reason error. It's not important 
         * at this level. */
        onCancelSuccess()
      }
    }
  }
}

/* We want to get and set values from the promise, and we also want to catch errors. */
export const _set = function(result) {
  return result.set
}

/* To get a value, we need to handle */
export const _get = function(result) {
  return result.get
}

export const _error = function(result) {
  return result.error
}