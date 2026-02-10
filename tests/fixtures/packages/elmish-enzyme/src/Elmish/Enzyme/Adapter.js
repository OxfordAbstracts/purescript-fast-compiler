export function adapterImpl(pkg) {
  return () => {
    const Adapter = import(pkg)
    return Adapter.then(m => {
      const Adaptr = m.default;
      return function () { return new Adaptr()}} )
  };
}
