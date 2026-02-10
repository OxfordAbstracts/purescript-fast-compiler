import * as go from 'gojs';

export const isInstanceOf = (obj) => (className) => {
    return obj instanceof go[className];
}