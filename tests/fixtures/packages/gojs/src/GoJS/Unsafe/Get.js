export const getAttrs = (attrs) => (d) => {
    iter = d;
    for (i in attrs) {
        iter = iter[attrs[i]];
    }
    return iter;
}