import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var emptySet = function (v) {
    return true;
};
var elem = function (x) {
    return function (f) {
        return f(x);
    };
};
var test2 = /* #__PURE__ */ elem(1)(emptySet);
var compose = function (f) {
    return function (g) {
        return function (a) {
            return f(g(a));
        };
    };
};
var test1 = /* #__PURE__ */ compose(function (x) {
    return x;
})(function (y) {
    return y;
});
export {
    compose,
    test1,
    elem,
    emptySet,
    test2,
    main
};
