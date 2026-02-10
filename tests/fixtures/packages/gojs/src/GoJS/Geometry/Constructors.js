import * as go from 'gojs';

export const newGeometry = (figs) => (spot1) => (spot2) => {
    geo = new go.Geometry();
    for (i in figs) {
        geo.add(figs[i])
    }
    geo.spot1 = spot1;
    geo.spot2 = spot2;
    return geo;
};
