import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var decode = function (dict) {
    return dict.decode;
};
var decodeField = function (dictDecode) {
    var decode1 = decode(dictDecode);
    return function () {
        return function (v) {
            return decode1("");
        };
    };
};
export {
    decode,
    decodeField,
    main
};
