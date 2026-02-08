import { JSDOM } from 'jsdom';

export const _jsdom = (html, constructorOptions) => new JSDOM(html, constructorOptions)
export const _window = jsdom => jsdom.window
export const _document = jsdomWindow => jsdomWindow.document
