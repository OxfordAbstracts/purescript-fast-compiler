export const _bufferType = buffer => () => buffer.type;
export const cursorY = buffer => () => buffer.cursorY;
export const cursorX = buffer => () => buffer.cursorX;
export const viewportY = buffer => () => buffer.viewportY;
export const baseY = buffer => () => buffer.baseY;
export const length = buffer => () => buffer.length;
export const _getLine = buffer => l => () => buffer.getLine(l);
export const getNullCell = buffer => () => buffer.getNullCell();
