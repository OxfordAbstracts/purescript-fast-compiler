import * as go from 'gojs';

export const newSpot = (x) => (y) => (offx) => (offy) => {
    return new go.Spot(x, y, offx, offy)
}

export const topSide_ = go.Spot.TopSide
export const topBottomSides_ = go.Spot.TopBottomSides
export const topLeftSides_ = go.Spot.TopLeftSides
export const topRightSides_ = go.Spot.TopRightSides
export const bottomSide_ = go.Spot.BottomSide
export const bottomLeftSides_ = go.Spot.BottomLeftSides
export const bottomRightSides_ = go.Spot.BottomRightSides
export const leftRightSides_ = go.Spot.LeftRightSides
export const leftSide_ = go.Spot.LeftSide
export const rightSide_ = go.Spot.RightSide