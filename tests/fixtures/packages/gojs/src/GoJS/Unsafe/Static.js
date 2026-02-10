import * as go from 'gojs';

export const callStatic0 = (className) => (methodName) => () => {
    return go[className][methodName]();
}

export const callStatic1 = (className) => (methodName) => (arg1) => () => {
    return go[className][methodName](arg1);
}

export const callStatic2 = (className) => (methodName) => (arg1) => (arg2) => () => {
    return go[className][methodName](arg1, arg2);
}

export const callStatic3 = (className) => (methodName) => (arg1) => (arg2) => (arg3) => () => {
    return go[className][methodName](arg1, arg2, arg3);
}
export const callStatic4 = (className) => (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => () => {
    return go[className][methodName](arg1, arg2, arg3, arg4);
}
export const callStatic5 = (className) => (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => (arg5) => () => {
    return go[className][methodName](arg1, arg2, arg3, arg4, arg5);
}

export const callStaticPure1 = (className) => (methodName) => (arg1) => {
    return go[className][methodName](arg1);
}

export const callStaticPure2 = (className) => (methodName) => (arg1) => (arg2) => {
    return go[className][methodName](arg1, arg2);
}

export const callStaticPure3 = (className) => (methodName) => (arg1) => (arg2) => (arg3) => {
    return go[className][methodName](arg1, arg2, arg3);
}
export const callStaticPure4 = (className) => (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => {
    return go[className][methodName](arg1, arg2, arg3, arg4);
}
export const callStaticPure5 = (className) => (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => (arg5) => {
    return go[className][methodName](arg1, arg2, arg3, arg4, arg5);
}

export const callStaticPure6 = (className) => (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => (arg5) => (arg6) => {
    return go[className][methodName](arg1, arg2, arg3, arg4, arg5, arg6);
}
export const callStaticPure7 = (className) => (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => (arg5) => (arg6) => (arg7) => {
    return go[className][methodName](arg1, arg2, arg3, arg4, arg5, arg6, arg7);
}