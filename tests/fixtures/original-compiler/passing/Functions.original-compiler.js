import * as Effect_Console from "../Effect.Console/index.js";
var test3 = function (a) {
    return a;
};
var test2 = function (a) {
    return function (b) {
        return a + b + 1.0;
    };
};
var test1 = function (v) {
    return 0.0;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    test1,
    test2,
    test3,
    main
};
