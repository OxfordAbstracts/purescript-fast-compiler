import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var ctorKind1 = {};
var ctorKind0 = function () {
    return {};
};
var ctorKind = function () {
    return function (v) {
        return $$Proxy.value;
    };
};
var ctorKind2 = /* #__PURE__ */ ctorKind();
var testCtor1 = /* #__PURE__ */ (function () {
    return ctorKind2($$Proxy.value);
})();
var testCtor2 = /* #__PURE__ */ (function () {
    return ctorKind2($$Proxy.value);
})();
var testCtor3 = /* #__PURE__ */ (function () {
    return ctorKind2($$Proxy.value);
})();
export {
    $$Proxy as Proxy,
    ctorKind,
    testCtor1,
    testCtor2,
    testCtor3,
    main,
    ctorKind0,
    ctorKind1
};
