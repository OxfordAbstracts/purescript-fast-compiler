import * as Control_Category from "../Control.Category/index.js";
import * as Data_Array_Partial from "../Data.Array.Partial/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var head = /* #__PURE__ */ Data_Array_Partial.head();
var tail = /* #__PURE__ */ Data_Array_Partial.tail();
var logShow = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showInt);
var sumTCObug$prime = /* #__PURE__ */ (function () {
    var go = function ($copy_v) {
        return function ($copy_v1) {
            var $tco_var_v = $copy_v;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(v, v1) {
                if (v1 === 0) {
                    $tco_done = true;
                    return v;
                };
                $tco_var_v = function (a) {
                    return v1 + a | 0;
                };
                $copy_v1 = 0;
                return;
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_v, $copy_v1);
            };
            return $tco_result;
        };
    };
    return go(identity);
})();
var sumTCObug = /* #__PURE__ */ (function () {
    var go = function ($copy_v) {
        return function ($copy_v1) {
            var $tco_var_v = $copy_v;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(v, v1) {
                if (v1 === 0) {
                    $tco_done = true;
                    return v;
                };
                var f$prime = function (a) {
                    return v1 + a | 0;
                };
                $tco_var_v = f$prime;
                $copy_v1 = 0;
                return;
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_v, $copy_v1);
            };
            return $tco_result;
        };
    };
    return go(identity);
})();
var count = function (p) {
    var count$prime = function ($copy_v) {
        return function ($copy_v1) {
            var $tco_var_v = $copy_v;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(v, v1) {
                if (v1.length === 0) {
                    $tco_done = true;
                    return v;
                };
                var h = head(v1);
                $tco_var_v = v + (function () {
                    var $24 = p(h);
                    if ($24) {
                        return 1;
                    };
                    return 0;
                })() | 0;
                $copy_v1 = tail(v1);
                return;
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_v, $copy_v1);
            };
            return $tco_result;
        };
    };
    return count$prime(0);
};
var main = /* #__PURE__ */ (function () {
    var z = count(function (v) {
        return v > 0;
    })([ -1 | 0, 0, 1 ]);
    var y = sumTCObug$prime(7)(3);
    var x = sumTCObug(7)(3);
    return function __do() {
        logShow(x)();
        logShow(y)();
        logShow(z)();
        var $25 = x === 10 && (y === 10 && z === 1);
        if ($25) {
            return Effect_Console.log("Done")();
        };
        return Effect_Console.log("Fail")();
    };
})();
export {
    sumTCObug,
    sumTCObug$prime,
    count,
    main
};
