import * as go from 'gojs';

export const pathFigure_ = (sx) => (sy) => (filled) => (shadowed) => (isEvenOdd) => (segs) => {
    fig = new go.PathFigure(sx, sy, filled, shadowed, isEvenOdd);
    for (i in segs) {
        fig.add(segs[i])
    }
    return fig;
}
