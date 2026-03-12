import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fn1 = function () {
    return function () {
        return function (v) {
            return "";
        };
    };
};
var fn2 = function (dictFD) {
    var fn11 = fn1(dictFD);
    return function (dictC) {
        var fn12 = fn11(dictC);
        return function (x) {
            return fn12(x);
        };
    };
};
export {
    fn1,
    fn2,
    main
};
