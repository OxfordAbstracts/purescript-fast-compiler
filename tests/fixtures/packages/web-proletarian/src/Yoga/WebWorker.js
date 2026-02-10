export const subscribe = handler => () => {
  addEventListener("message", (event) => {
    handler(event.data)();
  })
}

export const quit = () => close()

export const postMessageToBoss = data => () => postMessage(data)

