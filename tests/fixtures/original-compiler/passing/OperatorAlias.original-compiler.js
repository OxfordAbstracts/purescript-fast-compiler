import * as Effect_Console from "../Effect.Console/index.js";
var what = function (a) {
    return function (v) {
        return a;
    };
};
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ what("Done")(true));
export {
    what,
    main
};
