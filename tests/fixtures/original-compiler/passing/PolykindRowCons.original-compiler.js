import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var Identity = /* #__PURE__ */ (function () {
    function Identity(value0) {
        this.value0 = value0;
    };
    Identity.create = function (value0) {
        return new Identity(value0);
    };
    return Identity;
})();
var App = /* #__PURE__ */ (function () {
    function App(value0) {
        this.value0 = value0;
    };
    App.create = function (value0) {
        return new App(value0);
    };
    return App;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var lookup = function () {
    return function (v) {
        return function (v1) {
            return $$Proxy.value;
        };
    };
};
var lookup10 = /* #__PURE__ */ lookup();
var lookup1 = /* #__PURE__ */ (function () {
    return lookup10($$Proxy.value)($$Proxy.value);
})();
var test1 = lookup1;
var lookup2 = /* #__PURE__ */ (function () {
    return lookup10($$Proxy.value)($$Proxy.value);
})();
var test2 = lookup2;
var lookup3 = /* #__PURE__ */ (function () {
    return lookup10($$Proxy.value)($$Proxy.value);
})();
var test3 = lookup3;
var lookup4 = /* #__PURE__ */ (function () {
    return lookup10($$Proxy.value)($$Proxy.value);
})();
var test4 = lookup4;
var lookup5 = /* #__PURE__ */ (function () {
    return lookup10($$Proxy.value)($$Proxy.value);
})();
var test5 = lookup5;
var lookup6 = /* #__PURE__ */ (function () {
    return lookup10($$Proxy.value)($$Proxy.value);
})();
var test6 = lookup6;
var lookup7 = /* #__PURE__ */ (function () {
    return lookup10($$Proxy.value)($$Proxy.value);
})();
var test7 = lookup7;
var lookup8 = /* #__PURE__ */ (function () {
    return lookup10($$Proxy.value)($$Proxy.value);
})();
var test8 = lookup8;
var lookup9 = /* #__PURE__ */ (function () {
    return lookup10($$Proxy.value)($$Proxy.value);
})();
var test9 = lookup9;
export {
    $$Proxy as Proxy,
    Identity,
    App,
    lookup,
    lookup1,
    lookup2,
    lookup3,
    lookup4,
    lookup5,
    lookup6,
    lookup7,
    lookup8,
    lookup9,
    test1,
    test2,
    test3,
    test4,
    test5,
    test6,
    test7,
    test8,
    test9,
    main
};
