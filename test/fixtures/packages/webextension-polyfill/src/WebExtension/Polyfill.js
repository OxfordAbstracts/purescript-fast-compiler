import browser, { storage, history as _history, runtime, windows } from 'webextension-polyfill'

export const browserImpl = browser
export function loadFromLocalStorageImpl(key) { return () => storage.local.get(key)}
export function saveInLocalStorageImpl(obj) { return () => storage.local.set(obj)}
export function removeFromLocalStorageImpl(key) { return () => storage.local.remove(key)}

export function history() { return _history}

export function addOnVisitedListenerImpl(listener) { return history => () => history.onVisited.addListener(listener)}

export function sendMessageViaPortImpl(message, port) { return port.postMessage(message)}
export function addOnPortMessageListenerImpl(listener, port) { return port.onMessage.addListener(listener)}

export function onContentScriptConnectedImpl(listener) { return () =>
  runtime.onConnect.addListener(port => listener(port)())}

export const connectToBackgroundScriptImpl = runtime.connect

export function openNewWindowImpl(options) { return () => windows.create(options)}

export const reload = runtime.reload