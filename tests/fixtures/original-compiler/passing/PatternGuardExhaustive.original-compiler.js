import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var classify = function (v) {
    if (v.length === 0) {
        return 0;
    };
    if (v.length === 1) {
        return 1;
    };
    if (v.length === 2) {
        return 2;
    };
    var $6 = {
        len: 3
    };
    return $6.len;
};
export {
    classify,
    main
};
