import * as Effect_Console from "../Effect.Console/index.js";
var y = function (a) {
    return x(a);
};
var x = function (a) {
    return 1.0 + y(a);
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    x,
    y,
    main
};
