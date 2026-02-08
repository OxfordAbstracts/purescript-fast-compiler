import * as d3TimeFormat from "d3-time-format";

export const timeFormat = d3TimeFormat.timeFormat;

export function localeTimeFormat(str) {
  return (locale) => locale.format(str);
}

export function timeFormatLocale(def) {
  return d3TimeFormat.timeFormatLocale(def);
}
