import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var reflIsEq = {};
var reflArg = {};
var notIsEq = {};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var learnIsString = function () {
    return function () {
        return function (v) {
            return $$Proxy.value;
        };
    };
};
var learnIsString1 = /* #__PURE__ */ learnIsString()();
var learnInst = {};
var isStringString = {};
var isStringElse = {};
var isStringEg1 = /* #__PURE__ */ (function () {
    return learnIsString1($$Proxy.value);
})();
var isStringEg0 = /* #__PURE__ */ (function () {
    return learnIsString1($$Proxy.value);
})();
var isEq = function () {
    return function (v) {
        return function (v1) {
            return $$Proxy.value;
        };
    };
};
var isEq1 = /* #__PURE__ */ isEq();
var isEqEg0 = /* #__PURE__ */ (function () {
    return isEq1($$Proxy.value)($$Proxy.value);
})();
var isEqEg1 = /* #__PURE__ */ (function () {
    return isEq1($$Proxy.value)($$Proxy.value);
})();
var isEqEg2 = /* #__PURE__ */ (function () {
    return isEq1($$Proxy.value)($$Proxy.value);
})();
var arg = function () {
    return function (v) {
        return $$Proxy.value;
    };
};
var arg1 = /* #__PURE__ */ arg();
var argEg0 = /* #__PURE__ */ (function () {
    return arg1($$Proxy.value);
})();
var appArg = function () {
    return {};
};
var argEg1 = /* #__PURE__ */ (function () {
    return arg1($$Proxy.value);
})();
var argEg2 = /* #__PURE__ */ (function () {
    return arg1($$Proxy.value);
})();
export {
    $$Proxy as Proxy,
    arg,
    argEg0,
    argEg1,
    argEg2,
    isEq,
    isEqEg0,
    isEqEg1,
    isEqEg2,
    learnIsString,
    isStringEg0,
    isStringEg1,
    main,
    appArg,
    reflArg,
    reflIsEq,
    notIsEq,
    learnInst,
    isStringString,
    isStringElse
};
