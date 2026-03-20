import * as Effect_Console from "../Effect.Console/index.js";
var not = function (x) {
    if (x) {
        return false;
    };
    return true;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fns = function (f) {
    var $1 = f(true);
    if ($1) {
        return f;
    };
    return function (x) {
        return x;
    };
};
export {
    fns,
    not,
    main
};
