import * as Effect_Console from "../Effect.Console/index.js";
var testUnit = {};
var test = function () {
    return function (a) {
        return a;
    };
};
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ test()("Done"));
export {
    test,
    main,
    testUnit
};
