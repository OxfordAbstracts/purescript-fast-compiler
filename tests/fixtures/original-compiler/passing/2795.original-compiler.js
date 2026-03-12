import * as Data_Boolean from "../Data.Boolean/index.js";
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
var Y = /* #__PURE__ */ (function () {
    function Y() {

    };
    Y.value = new Y();
    return Y;
})();
var x = function (v) {
    if (v instanceof Y) {
        return 0;
    };
    var v1 = function (v2) {
        if (v instanceof X && Data_Boolean.otherwise) {
            return 2;
        };
        throw new Error("Failed pattern match at Main (line 8, column 1 - line 8, column 14): " + [ v.constructor.name ]);
    };
    if (v instanceof X) {
        if (v.value0 === 1) {
            return 1;
        };
        return v1(true);
    };
    return v1(true);
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    X,
    Y,
    x,
    main
};
