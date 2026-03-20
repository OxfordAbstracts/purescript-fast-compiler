import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var $runtime_lazy = function (name, moduleName, init) {
    var state = 0;
    var val;
    return function (lineNumber) {
        if (state === 2) return val;
        if (state === 1) throw new ReferenceError(name + " was needed before it finished initializing (module " + moduleName + ", line " + lineNumber + ")", moduleName, lineNumber);
        state = 1;
        val = init();
        state = 2;
        return val;
    };
};
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var show1 = /* #__PURE__ */ Data_Show.show(/* #__PURE__ */ Data_Show.showArray(Data_Show.showNumber));
var logShow = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showNumber);
var $lazy_f = /* #__PURE__ */ $runtime_lazy("f", "Main", function () {
    return function (a, b) {
        return $lazy_g(8)(a, b) + $lazy_g(8)(b, a);
    };
});
var $lazy_g = /* #__PURE__ */ $runtime_lazy("g", "Main", function () {
    return function (a, b) {
        var $11 = {};
        if (a <= 0.0 || b <= 0.0) {
            return b;
        };
        return $lazy_f(12)(a - 0.0, b - 0.0);
    };
});
var f = /* #__PURE__ */ $lazy_f(8);
var g = /* #__PURE__ */ $lazy_g(10);
var main = function __do() {
    Effect_Console.log(show(0.0))();
    (function (a) {
        return Effect_Console.log(show(a));
    })(0.0)();
    (function (a, b) {
        return Effect_Console.log(show1([ a, b ]));
    })(0.0, 0.0)();
    (function (a, b, c) {
        return Effect_Console.log(show1([ a, b, c ]));
    })(0.0, 0.0, 0.0)();
    (function (a, b, c, d) {
        return Effect_Console.log(show1([ a, b, c, d ]));
    })(0.0, 0.0, 0.0, 0.0)();
    (function (a, b, c, d, e) {
        return Effect_Console.log(show1([ a, b, c, d, e ]));
    })(0.0, 0.0, 0.0, 0.0, 0.0)();
    (function (a, b, c, d, e, f1) {
        return Effect_Console.log(show1([ a, b, c, d, e, f1 ]));
    })(0.0, 0.0, 0.0, 0.0, 0.0, 0.0)();
    (function (a, b, c, d, e, f1, g1) {
        return Effect_Console.log(show1([ a, b, c, d, e, f1, g1 ]));
    })(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)();
    (function (a, b, c, d, e, f1, g1, h) {
        return Effect_Console.log(show1([ a, b, c, d, e, f1, g1, h ]));
    })(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)();
    (function (a, b, c, d, e, f1, g1, h, i) {
        return Effect_Console.log(show1([ a, b, c, d, e, f1, g1, h, i ]));
    })(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)();
    (function (a, b, c, d, e, f1, g1, h, i, j) {
        return Effect_Console.log(show1([ a, b, c, d, e, f1, g1, h, i, j ]));
    })(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)();
    logShow(g(0.0, 0.0))();
    return Effect_Console.log("Done")();
};
export {
    f,
    g,
    main
};
