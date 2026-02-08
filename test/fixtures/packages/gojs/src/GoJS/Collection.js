export const iterate_ = (i) => {
    if (i.next()) {
        return i.value
    } else return null;
}

export const toIterator_ = (s) => {
    return s.iterator;
}

export const setFirst_ = (s) => {
    return s.first();
}

export const insertAt_ = (i) => (val) => (list) => () => {
    list.insertAt(i, val);
}
