"use strict";

export function urlSearchParamsImpl(x) {
    return new URLSearchParams(x);
}

export function appendImpl(name) {
    return function(value) {
        return function(p) {
            var n = new URLSearchParams(p);
            n.append(name, value);
            return n;
        }
    }
}

export function deleteImpl(name) {
    return function(p) {
        var n = new URLSearchParams(p);
        n.delete(name);
        return n;
    }
}

export function entriesImpl(tuple) {
    return function(p) {
        var a = [];
        for (const e of p.entries()) {
            a.push(tuple(e[0])(e[1]));
        }
        return a;
    }
}

export function getImpl(just) {
    return function(nothing) {
        return function(name) {
            return function(p) {
                var v = p.get(name);
                if (v === null) {
                    return nothing;
                } else {
                    return just(v);
                }
            }
        }
    }
}

export function getAllImpl(name) {
    return function(p) {
        return p.getAll(name);
    }
}

export function hasImpl(name) {
    return function(p) {
        return p.has(name);
    }
}

export function setImpl(name) {
    return function(value) {
        return function(p) {
            var n = new URLSearchParams(p);
            n.set(name, value);
            return n;
        }
    }
}

export function sortImpl(p) {
    var n = new URLSearchParams(p);
    n.sort();
    return n;
}

export function toStringImpl(p) {
    return p.toString();
}
