import * as Effect_Console from "../Effect.Console/index.js";
var X = /* #__PURE__ */ (function () {
    function X(value0) {
        this.value0 = value0;
    };
    X.create = function (value0) {
        return new X(value0);
    };
    return X;
})();
var Z = /* #__PURE__ */ (function () {
    function Z() {

    };
    Z.value = new Z();
    return Z;
})();
var Y = /* #__PURE__ */ (function () {
    function Y(value0) {
        this.value0 = value0;
    };
    Y.create = function (value0) {
        return new Y(value0);
    };
    return Y;
})();
var test4 = /* #__PURE__ */ (function () {
    return new Y(new X(new Y(Z.value)));
})();
var test3 = /* #__PURE__ */ (function () {
    return new Y(new X(new Y(Z.value)));
})();
var test2 = /* #__PURE__ */ (function () {
    return new X(new Y(Z.value));
})();
var test1 = /* #__PURE__ */ (function () {
    return new X(new Y(Z.value));
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    X,
    Z,
    Y,
    test1,
    test2,
    test3,
    test4,
    main
};
