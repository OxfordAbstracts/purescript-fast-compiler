export const callUnsafe0 = (methodName) => (obj) => () => {
    return obj[methodName]();
}

export const callUnsafe1 = (methodName) => (arg1) => (obj) => () => {
    return obj[methodName](arg1);
}


export const callUnsafe2 = (methodName) => (arg1) => (arg2) => (obj) => () => {
    return obj[methodName](arg1, arg2);
}

export const callUnsafe3 = (methodName) => (arg1) => (arg2) => (arg3) => (obj) => () => {
    return obj[methodName](arg1, arg2, arg3);
}

export const callUnsafe4 = (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => (obj) => () => {
    return obj[methodName](arg1, arg2, arg3, arg4);
}

export const callUnsafe5 = (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => (arg5) => (obj) => () => {
    return obj[methodName](arg1, arg2, arg3, arg4, arg5);
}

export const callUnsafe6 = (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => (arg5) => (arg6) => (obj) => () => {
    return obj[methodName](arg1, arg2, arg3, arg4, arg5, arg6);
}

export const callUnsafe7 = (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => (arg5) => (arg6) => (arg7) => (obj) => () => {
    return obj[methodName](arg1, arg2, arg3, arg4, arg5, arg6, arg7);
}

export const callUnsafe8 = (methodName) => (arg1) => (arg2) => (arg3) => (arg4) => (arg5) => (arg6) => (arg7) => (arg8) => (obj) => () => {
    return obj[methodName](arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8);
}
