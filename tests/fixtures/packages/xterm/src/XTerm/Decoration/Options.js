export const makeDecorationOptions = d => {
  const a = { marker: d.marker };
  const b = d.decorationOptions;
  return { ...a, ...b }
}
