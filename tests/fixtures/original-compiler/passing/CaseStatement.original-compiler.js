import * as Effect_Console from "../Effect.Console/index.js";
var N = /* #__PURE__ */ (function () {
    function N() {

    };
    N.value = new N();
    return N;
})();
var J = /* #__PURE__ */ (function () {
    function J(value0) {
        this.value0 = value0;
    };
    J.create = function (value0) {
        return new J(value0);
    };
    return J;
})();
var A = /* #__PURE__ */ (function () {
    function A() {

    };
    A.value = new A();
    return A;
})();
var B = /* #__PURE__ */ (function () {
    function B() {

    };
    B.value = new B();
    return B;
})();
var C = /* #__PURE__ */ (function () {
    function C() {

    };
    C.value = new C();
    return C;
})();
var h = function (v) {
    return function (v1) {
        return function (v2) {
            if (v1 instanceof N) {
                return v2;
            };
            if (v2 instanceof N) {
                return v1;
            };
            if (v1 instanceof J && v2 instanceof J) {
                return new J(v(v1.value0)(v2.value0));
            };
            throw new Error("Failed pattern match at Main (line 18, column 1 - line 18, column 12): " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
        };
    };
};
var g = function (v) {
    return function (v1) {
        return function (v2) {
            if (v2 instanceof A) {
                return v;
            };
            if (v2 instanceof B) {
                return v1;
            };
            if (v2 instanceof C) {
                return C.value;
            };
            throw new Error("Failed pattern match at Main (line 12, column 1 - line 12, column 12): " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
        };
    };
};
var f = function (v) {
    return function (v1) {
        return function (v2) {
            if (v2 instanceof A) {
                return v;
            };
            if (v2 instanceof B) {
                return v1;
            };
            if (v2 instanceof C) {
                return "Done";
            };
            throw new Error("Failed pattern match at Main (line 8, column 1 - line 8, column 12): " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
        };
    };
};
var main = /* #__PURE__ */ (function () {
    return Effect_Console.log(f("Done")("Failed")(A.value));
})();
export {
    A,
    B,
    C,
    f,
    g,
    N,
    J,
    h,
    main
};
