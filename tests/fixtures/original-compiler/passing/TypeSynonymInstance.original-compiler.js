import * as Effect_Console from "../Effect.Console/index.js";
var convertSB = {
    convert: function (v) {
        if (v === 0) {
            return "Nope";
        };
        return "Done";
    }
};
var convert = function (dict) {
    return dict.convert;
};
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ convert(convertSB)(1));
export {
    convert,
    main,
    convertSB
};
