'use strict';

export function dispatchEvent(evt) {
  return function(window_) {
    return function() {
      window_.dispatchEvent(new Event(evt));
    }
  }
}
