export const active = ns => ns.active;
export const normal = ns => ns.normal;
export const alternate = ns => ns.alternate;
export const onBufferChange = ns => listener => () => ns.onBufferChange(b => listener(b)());
