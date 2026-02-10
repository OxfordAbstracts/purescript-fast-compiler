export const ffilog = (x) => () => {
    console.log(x, typeof x);
}

export const trace = (x) => {
    console.log(x);
    return x;
}
