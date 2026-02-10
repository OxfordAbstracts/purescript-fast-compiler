import * as go from 'gojs';

export const newRect = (x) => (y) => (w) => (h) => {
    return new go.Rect(x, y, w, h)
}
