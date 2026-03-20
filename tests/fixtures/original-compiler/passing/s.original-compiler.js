import * as Effect_Console from "../Effect.Console/index.js";
var s = function (x) {
    return function (y) {
        return function (z) {
            return x(z)(y(z));
        };
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    s,
    main
};
