export const _makeLink = range => text => activate => opts => {
  var link = { range: range, text: text, activate: (e,s) => activate(e)(s)() };
  link = opts.decorations ? link.decorations = opts.decorations : link;
  link = opts.hover ? link.hover = (e,s) => opts.hover(e)(s)() : link;
  link = opts.leave ? link.leave = (e,s) => opts.leave(e)(s)() : link;
  link = opts.dispose ? link.dispose = opts.dispose : link;
  return link;
}
