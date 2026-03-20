import * as Effect_Console from "../Effect.Console/index.js";
var f2 = function (v) {
    return "Done";
};
var f1 = function (g) {
    return g(1);
};
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ f1(f2));
export {
    f1,
    f2,
    main
};
