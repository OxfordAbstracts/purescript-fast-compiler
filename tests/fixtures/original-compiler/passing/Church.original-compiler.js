import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var empty = function (r) {
    return function (f) {
        return r;
    };
};
var cons = function (a) {
    return function (l) {
        return function (r) {
            return function (f) {
                return f(a)(l(r)(f));
            };
        };
    };
};
var append = function (l1) {
    return function (l2) {
        return function (r) {
            return function (f) {
                return l2(l1(r)(f))(f);
            };
        };
    };
};
var test = /* #__PURE__ */ append(/* #__PURE__ */ cons(1)(empty))(/* #__PURE__ */ cons(2)(empty));
export {
    empty,
    cons,
    append,
    test,
    main
};
