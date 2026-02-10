export const marker = d => d.marker;
export const onRender = d => callback => () => d.onRender(e => callback(e)());
export const _getElement = d => () => d.element;
export const _overviewRuler = d => d.options ? d.options.overviewRulerOptions : d.options;

