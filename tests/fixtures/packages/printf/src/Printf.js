/**
 * 
 * @param {string} controls 
 * @returns {(value:number) => string}
 */
export const formatFloat = (controls) => (value) => {
  const [, sign, left, fill, width, decimals] =
    /^(\+)?(-)?('.|0)?(\d+)?(?:\.(\d*))?$/.exec(controls) || [];

  const maxWidth = Number(width) || 0;
  const decimalPlaces = Number(decimals);
  const padding = fill?.replace("'", '') || ' ';

  const num = Number.isNaN(decimalPlaces) ?
    String(Math.abs(value)) :
    Math.abs(value).toFixed(decimalPlaces);
  const prefix = value < 0 ? '-' : (sign && value > 0 ? '+' : '');

  if (padding === '0' && !left) {
    return `${prefix}${num.padStart(maxWidth - prefix.length, '0')}`;
  }

  const formattedNum = `${prefix}${num}`;
  return left ?
    formattedNum.padEnd(maxWidth, padding) :
    formattedNum.padStart(maxWidth, padding);
}

/**
 * 
 * @param {string} controls 
 * @returns {(value:number) => string}
 */
export const formatInt = formatFloat;

/**
 * 
 * @param {string} controls 
 * @returns {(value:string) => string}
 */
export const formatString = (controls) => (value) => {
  const [, , left, fill, width,] =
    /^(\+)?(-)?('.|0)?(\d+)?(?:\.(\d*))?$/.exec(controls) || [];

  const maxWidth = Number(width) || 0;
  const padding = fill?.replace("'", '') || ' ';

  return left ?
    value.padEnd(maxWidth, padding) :
    value.padStart(maxWidth, padding);
}
