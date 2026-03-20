import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var f = function (x) {
    var g = function (x1) {
        var go1 = function (x2) {
            return go(x2);
        };
        var go = function (x2) {
            return go1(x2 - 1.0);
        };
        return go(x1);
    };
    return g(x);
};
export {
    f,
    main
};
