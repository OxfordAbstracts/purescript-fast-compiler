import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var Pair = /* #__PURE__ */ (function () {
    function Pair() {

    };
    Pair.value = new Pair();
    return Pair;
})();
var B = /* #__PURE__ */ (function () {
    function B() {

    };
    B.value = new B();
    return B;
})();
var A = /* #__PURE__ */ (function () {
    function A() {

    };
    A.value = new A();
    return A;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var k = function (v) {
    return 42;
};
var test = /* #__PURE__ */ (function () {
    return k($$Proxy.value);
})();
export {
    A,
    B,
    Pair,
    $$Proxy as Proxy,
    k,
    test,
    main
};
