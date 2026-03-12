import * as Effect_Console from "../Effect.Console/index.js";
var X = /* #__PURE__ */ (function () {
    function X() {

    };
    X.value = new X();
    return X;
})();
var Y = /* #__PURE__ */ (function () {
    function Y() {

    };
    Y.value = new Y();
    return Y;
})();
var what = function (v) {
    if (v) {
        return X.value;
    };
    return Y.value;
};
var cond = function (v) {
    return function (v1) {
        return function (v2) {
            if (v) {
                return v1;
            };
            return v2;
        };
    };
};
var main = /* #__PURE__ */ (function () {
    var tmp2 = cond(true)(0)(1);
    var tmp1 = what(true);
    return Effect_Console.log("Done");
})();
export {
    X,
    Y,
    cond,
    what,
    main
};
