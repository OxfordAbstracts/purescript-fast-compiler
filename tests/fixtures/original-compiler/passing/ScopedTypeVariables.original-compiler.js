import * as Effect_Console from "../Effect.Console/index.js";
var test4 = /* #__PURE__ */ (function () {
    var h = function (f) {
        return function (x) {
            var g = function (y) {
                var j = function (x1) {
                    return x1;
                };
                return j(f(f(y)));
            };
            return g(g(x));
        };
    };
    return h;
})();
var test3 = /* #__PURE__ */ (function (b) {
    return b;
})(0.0);
var test2 = /* #__PURE__ */ (function () {
    var h = function (f) {
        return function (x) {
            var g = function (y) {
                return f(f(y));
            };
            return g(g(x));
        };
    };
    return h;
})();
var test1 = function (f) {
    return function (x) {
        var g = function (y) {
            return f(f(y));
        };
        return g(g(x));
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    test1,
    test2,
    test3,
    test4,
    main
};
