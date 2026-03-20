import * as Effect_Console from "../Effect.Console/index.js";
var test2 = {
    f: function (x) {
        return x;
    }
};
var test1 = {
    attr: function (v) {
        return 0;
    }
};
var test0 = function (v) {
    return 0;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var f = function (dict) {
    return dict.f;
};
export {
    f,
    test0,
    test1,
    main,
    test2
};
