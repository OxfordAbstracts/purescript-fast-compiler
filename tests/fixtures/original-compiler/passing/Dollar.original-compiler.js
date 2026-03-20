import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var id = function (x) {
    return x;
};
var applyFn = function (f) {
    return function (x) {
        return f(x);
    };
};
var test1 = function (x) {
    return applyFn(id)(applyFn(id)(applyFn(id)(applyFn(id)(x))));
};
var test2 = function (x) {
    return applyFn(id(id))(id(x));
};
export {
    applyFn,
    id,
    test1,
    test2,
    main
};
