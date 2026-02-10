import * as go from 'gojs';

export const pathSegmentLine_ = (ex) => (ey) => { return new go.PathSegment(go.PathSegment.Line, ex, ey); }
export const pathSegmentQuadraticBezier_ = (ex) => (ey) => (x1) => (y1) => { return new go.PathSegment(go.PathSegment.QuadraticBezier, ex, ey, x1, y1) }
export const pathSegmentBezier_ = (ex) => (ey) => (x1) => (y1) => (x2) => (y2) => { return new go.PathSegment(go.PathSegment.Bezier, ex, ey, x1, y1, x2, y2) }
export const pathSegmentArc_ = (startAngle) => (sweepAngle) => (centerX) => (centerY) => (radiusX) => (radiusY) => { return new go.PathSegment(go.PathSegment.Arc, startAngle, sweepAngle, centerX, centerY, radiusX, radiusY) }
export const pathSegmentSvgArc_ = (ex) => (ey) => (radiusX) => (radiusY) => (xAxisRotation) => (largeArcFlag) => (clockwiseFlag) => { return new go.PathSegment(go.PathSegment.SvgArc, ex, ey, radiusX, radiusY, xAxisRotation, largeArcFlag, clockwiseFlag) }
export const pathSegmentMove_ = (ex) => (ey) => { return new go.PathSegment(go.PathSegment(go.PathSegment.Move, ex, ey)) }
export const close_ = (pathSeg) => { return pathSeg.close() }