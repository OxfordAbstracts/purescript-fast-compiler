import { FitAddon } from 'xterm-addon-fit';
export const fitAddon = () => new FitAddon();
export const fit = addon => () => addon.fit();

