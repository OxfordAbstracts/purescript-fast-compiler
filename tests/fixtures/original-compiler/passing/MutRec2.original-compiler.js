import * as Effect_Console from "../Effect.Console/index.js";
var A = /* #__PURE__ */ (function () {
    function A(value0) {
        this.value0 = value0;
    };
    A.create = function (value0) {
        return new A(value0);
    };
    return A;
})();
var B = /* #__PURE__ */ (function () {
    function B(value0) {
        this.value0 = value0;
    };
    B.create = function (value0) {
        return new B(value0);
    };
    return B;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var g = function (b) {
    return f(b.value0);
};
var f = function (a) {
    return g(a.value0);
};
var showN = function (a) {
    return f(a);
};
export {
    A,
    B,
    f,
    g,
    showN,
    main
};
