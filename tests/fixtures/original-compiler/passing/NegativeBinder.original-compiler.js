import * as Effect_Console from "../Effect.Console/index.js";
var test2 = function (x) {
    return function (y) {
        if (x === -1.0 && y === -1.0) {
            return false;
        };
        return true;
    };
};
var test = function (v) {
    if (v === -1.0) {
        return false;
    };
    return true;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    test,
    test2,
    main
};
