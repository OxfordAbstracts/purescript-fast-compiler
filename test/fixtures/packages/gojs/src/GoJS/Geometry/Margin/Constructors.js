import * as go from 'gojs';

export const newMargin = (b) => (l) => (r) => (t) => {
    return new go.Margin(b, l, r, t);
};
