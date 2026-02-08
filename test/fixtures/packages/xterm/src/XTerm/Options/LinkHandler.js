export const makeLinkHandler = activate => h => {
    var linkHandler = { activate: (e,s,r) => activate(e)(s)(r)() };
    linkHandler = h.hover ? linkHandler.hover = (e,s,r) => h.hover(e)(s)(r)() : linkHandler;
    linkHandler = h.leave ? linkHandler.leave = (e,s,r) => h.leave(e)(s)(r)() : linkHandler;
    linkHandler = h.allowNonHttpProtocols ? linkHandler.allowNonHttpProtocols = h.allowNonHttpProtocols : linkHandler;
    return linkHandler
  }
