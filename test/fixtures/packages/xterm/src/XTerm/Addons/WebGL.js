import { WebglAddon } from 'xterm-addon-webgl';
export const webGLAddon = () => new WebglAddon();
export const onContextLoss = addon => callback => () => addon.onContextLoss(callback);

