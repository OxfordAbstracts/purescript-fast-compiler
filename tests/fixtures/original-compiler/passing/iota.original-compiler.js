import * as Effect_Console from "../Effect.Console/index.js";
var s = function (x) {
    return function (y) {
        return function (z) {
            return x(z)(y(z));
        };
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var k = function (x) {
    return function (y) {
        return x;
    };
};
var iota = function (x) {
    return x(s)(k);
};
export {
    s,
    k,
    iota,
    main
};
