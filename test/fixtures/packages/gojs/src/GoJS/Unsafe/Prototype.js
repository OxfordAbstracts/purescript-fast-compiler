import * as go from 'gojs';

export const prototypeArity0_ = (className) => (methodName) => (thisInstance) => {
    const method = go[className].prototype[methodName];
    return () => { return method.call(thisInstance) }
}

export const prototypeArity1_ = (className) => (methodName) => (thisInstance) => {
    const method = go[className].prototype[methodName];    
    return (arg) => () => { return method.call(thisInstance, arg) }
}

export const prototypeArity2_ = (className) => (methodName) => (thisInstance) => {
    const method = go[className].prototype[methodName];
    return (arg1) => (arg2) => () => { return method.call(thisInstance, arg1, arg2) }
}

export const prototypeArity3_ = (className) => (methodName) => (thisInstance) => {
    const method = go[className].prototype[methodName];
    return (arg1) => (arg2) => (arg3) => () => { return method.call(thisInstance, arg1, arg2, arg3) }
}

export const prototypeArity4_ = (className) => (methodName) => (thisInstance) => {
    const method = go[className].prototype[methodName];
    return (arg1) => (arg2) => (arg3) => (arg4) => () => { return method.call(thisInstance, arg1, arg2, arg3, arg4) }
}

export const prototypeArity5_ = (className) => (methodName) => (thisInstance) => {
    const method = go[className].prototype[methodName];
    return (arg1) => (arg2) => (arg3) => (arg4) => (arg5) => () => { return method.call(thisInstance, arg1, arg2, arg3, arg4, arg5) }
}