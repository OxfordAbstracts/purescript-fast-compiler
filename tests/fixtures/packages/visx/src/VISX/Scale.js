import { scaleLinear, scaleBand, scaleQuantize, scaleOrdinal, scaleTime } from "@visx/scale";

export const scaleLinearImpl = scaleLinear;
export const scaleBandImpl = scaleBand;
export const scaleQuantizeImpl = scaleQuantize;
export const scaleOrdinalImpl = scaleOrdinal;
export const scaleTimeImpl = scaleTime;
// exports.scaleUtcImpl = scale.scaleUtc;

export function bandwidth(bandScale) { return bandScale.bandwidth; }

export function scaleValueImpl(scale) { return (x) => scale(x); }
export function invertValueImpl(scale) { return (x) => scale.invert(x); }
