import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var F = /* #__PURE__ */ (function () {
    function F(value0) {
        this.value0 = value0;
    };
    F.create = function (value0) {
        return new F(value0);
    };
    return F;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fproxy = function (v) {
    return function (v1) {
        return $$Proxy.value;
    };
};
var a = /* #__PURE__ */ (function () {
    return fproxy($$Proxy.value);
})();
var b = /* #__PURE__ */ (function () {
    return a($$Proxy.value);
})();
var c = /* #__PURE__ */ (function () {
    return a($$Proxy.value);
})();
export {
    $$Proxy as Proxy,
    F,
    fproxy,
    a,
    b,
    c,
    main
};
