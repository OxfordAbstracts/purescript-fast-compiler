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
var what = function (x) {
    return function (v) {
        return function (v1) {
            if (v === 0 && (x instanceof X && v1)) {
                return X.value;
            };
            if (v === 0 && (x instanceof Y && v1)) {
                return X.value;
            };
            return Y.value;
        };
    };
};
var main = /* #__PURE__ */ (function () {
    var tmp = what(Y.value)(0)(true);
    return Effect_Console.log("Done");
})();
export {
    X,
    Y,
    what,
    main
};
