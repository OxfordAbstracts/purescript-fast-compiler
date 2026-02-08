export const onMessageFromWorker = handler => worker => () => { 
  worker.onmessage = (msg => handler(msg.data)()) 
}

export const postMessageToWorker = msg => worker => () => worker.postMessage(msg)

export const terminate = worker => () => worker.terminate()
