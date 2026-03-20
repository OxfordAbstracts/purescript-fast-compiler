import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var add = /* #__PURE__ */ Data_Semiring.add(Data_Semiring.semiringNumber);
var logShow = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showNumber);
var test7 = function (x) {
    var go = function ($copy_v) {
        var $tco_done = false;
        var $tco_result;
        function $tco_loop(v) {
            if (x - 0.1 < v * v && v * v < x + 0.1) {
                $tco_done = true;
                return v;
            };
            $copy_v = (v + x / v) / 2.0;
            return;
        };
        while (!$tco_done) {
            $tco_result = $tco_loop($copy_v);
        };
        return $tco_result;
    };
    return go(x);
};
var test6 = /* #__PURE__ */ (function () {
    var f = function (x) {
        return x;
    };
    var $16 = f(true);
    if ($16) {
        return f(1.0);
    };
    return f(2.0);
})();
var test5 = /* #__PURE__ */ (function () {
    var g = function (x) {
        return f(x - 1.0) + 1.0;
    };
    var f = function (v) {
        if (v > 0.0) {
            return g(v / 2.0) + 1.0;
        };
        return 0.0;
    };
    return g(10.0);
})();
var test4 = function (dictPartial) {
    var f = function (x) {
        return function (v) {
            if (v.length === 2) {
                return x(v[0])(v[1]);
            };
            throw new Error("Failed pattern match at Main (line 22, column 9 - line 22, column 27): " + [ x.constructor.name, v.constructor.name ]);
        };
    };
    return f(add)([ 1.0, 2.0 ]);
};
var test41 = /* #__PURE__ */ test4();
var test3 = /* #__PURE__ */ (function () {
    var f = function (x) {
        return function (y) {
            return function (z) {
                return x + y + z;
            };
        };
    };
    return f(1.0)(2.0)(3.0);
})();
var test2 = function (x) {
    return function (y) {
        var y$prime = y + 1.0;
        var x$prime = x + 1.0;
        return x$prime + y$prime;
    };
};
var test1 = function (x) {
    var y = x + 1.0;
    return y;
};
var main = function __do() {
    logShow(test1(1.0))();
    logShow(test2(1.0)(2.0))();
    logShow(test3)();
    logShow(test41)();
    logShow(test5)();
    logShow(test6)();
    logShow(test7(100.0))();
    return Effect_Console.log("Done")();
};
export {
    test1,
    test2,
    test3,
    test4,
    test5,
    test6,
    test7,
    main
};
