import * as Effect_Console from "../Effect.Console/index.js";
import * as MethodConstraintGiven_Lib from "../MethodConstraintGiven.Lib/index.js";
var Wrapper = function (x) {
    return x;
};
var ixMonadWrapper = {
    ipure: Wrapper
};
var ipure = /* #__PURE__ */ MethodConstraintGiven_Lib.ipure(ixMonadWrapper);
var ixBindWrapper = {
    ibind: function (v) {
        return function (f) {
            return f(v);
        };
    }
};
var ixApplyWrapper = {
    iapply: function (v) {
        return function (v1) {
            return ipure(v(v1));
        };
    },
    IxBind0: function () {
        return ixBindWrapper;
    },
    IxMonad1: function () {
        return ixMonadWrapper;
    }
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Wrapper,
    main,
    ixBindWrapper,
    ixMonadWrapper,
    ixApplyWrapper
};
