import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var appendProxy = function () {
    return function (v) {
        return function (v1) {
            return $$Proxy.value;
        };
    };
};
var appendNil = {};
var appendCons = function () {
    return {};
};
var test = /* #__PURE__ */ (function () {
    return appendProxy()($$Proxy.value)($$Proxy.value);
})();
export {
    $$Proxy as Proxy,
    appendProxy,
    test,
    main,
    appendNil,
    appendCons
};
