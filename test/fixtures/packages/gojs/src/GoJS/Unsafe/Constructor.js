import * as go from 'gojs';

export const constructor0 = (className) => () => {
    return new go[className]();
}

export const constructor1 = (className) => (arg1) => () => {
    return new go[className](arg1);
}

export const constructor2 = (className) => (arg1) => (arg2) => () => {
    return new go[className](arg1, arg2);
}

export const constructor3 = (className) => (arg1) => (arg2) => (arg3) => () => {
    return new go[className](arg1, arg2, arg3);
}

export const constructor4 = (className) => (arg1) => (arg2) => (arg3) => (arg4) => () => {
    return new go[className](arg1, arg2, arg3, arg4);
}

export const constructor5 = (className) => (arg1) => (arg2) => (arg3) => (arg4) => (arg5) => () => {
    return new go[className](arg1, arg2, arg3, arg4, arg5);
}