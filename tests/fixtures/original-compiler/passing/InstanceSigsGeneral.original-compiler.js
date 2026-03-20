import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var eqNumber = {
    eq: function (v) {
        return function (v1) {
            return true;
        };
    }
};
var eq = function (dict) {
    return dict.eq;
};
export {
    eq,
    main,
    eqNumber
};
