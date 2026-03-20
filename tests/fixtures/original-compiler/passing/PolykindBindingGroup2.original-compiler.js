import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var X = /* #__PURE__ */ (function () {
    function X(value0) {
        this.value0 = value0;
    };
    X.create = function (value0) {
        return new X(value0);
    };
    return X;
})();
var test2 = /* #__PURE__ */ (function () {
    return new X(function () {
        return $$Proxy.value;
    });
})();
var test1 = /* #__PURE__ */ (function () {
    return new X(function () {
        return $$Proxy.value;
    });
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    $$Proxy as Proxy,
    X,
    test1,
    test2,
    main
};
