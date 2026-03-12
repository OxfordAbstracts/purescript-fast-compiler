import * as Effect_Console from "../Effect.Console/index.js";
var test = function () {
    return function (v) {
        return function (v1) {
            return "Done";
        };
    };
};
var test1 = /* #__PURE__ */ test();
var eqAA = {};
var runTest = function (a) {
    return test1(a)(a);
};
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ runTest(0.0));
export {
    test,
    runTest,
    main,
    eqAA
};
