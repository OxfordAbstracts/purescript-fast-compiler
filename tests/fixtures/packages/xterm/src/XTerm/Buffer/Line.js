export const isWrapped = l => () => l.isWrapped;
export const length = l => () => l.length;
export const _getCell = l => x => () => l.getCell(x);
export const _getCellOpt = l => x => c => () => l.getCell(x,c);
export const translateToString = l => t => s => e => () => l.translateToString(t,s,e); 
