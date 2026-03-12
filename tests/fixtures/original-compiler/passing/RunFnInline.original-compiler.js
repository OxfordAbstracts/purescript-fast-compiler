import * as Effect_Console from "../Effect.Console/index.js";
var runFn3 = function (f) {
    return function (a) {
        return function (b) {
            return function (c) {
                return f(a)(b)(c);
            };
        };
    };
};
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ runFn3(function (a) {
    return function (b) {
        return function (c) {
            return c;
        };
    };
})(1)(2)("Done"));
export {
    runFn3,
    main
};
