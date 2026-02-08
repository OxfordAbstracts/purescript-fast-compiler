import * as go from 'gojs';

export const enumValueEq = (a) => (b) => {
    return a === b;
}

export const enumValueBuilder_ = (className) => (enumName) => { return go[className][enumName] }
