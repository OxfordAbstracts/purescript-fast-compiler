export const fromArrayImpl = (items) => {
    return [...items]
}

export const toArrayImpl = (items) => {
    return [...items]
}

export const shiftImpl = (items) => {
    items.shift()
}

export const unshiftImpl = (item, items) => {
    items.unshift(item)
}

export const pushImpl = (item, items) => {
    items.push(item)
}

export const foldlImpl = (f, acc_, items) => {
    let acc = acc_
    for (let i = 0; i < items.length; i++) {
        acc = f(acc, items[i])
    }

    return acc
}

export const foldrImpl = (f, acc_, items) => {
    let acc = acc_
    for (let i = items.length - 1; i >= 0; i--) {
        acc = f(items[i], acc)
    }

    return acc
}

export const popImpl = (items) => {
    items.pop()
}

export const lengthImpl = (items) => {
    return items.length
}

export const mapImpl = (f, items) => {
    const result = []
    for (let i = 0; i < items.length; i++) {
        result.push(f(items[i]))
    }

    return result
}

export const lookupImpl = (index, items) => {
    if (index < 0 || index >= items.length) {
        return null
    }

    return items[index]
}
