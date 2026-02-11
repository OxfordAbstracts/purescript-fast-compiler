const undefinedImpl = undefined;
export { undefinedImpl as undefined };
export const undefinable = (a, nothing, just) => a === undefined ? nothing : just(a);
