import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var assertEqual = /* #__PURE__ */ Test_Assert.assertEqual(Data_Eq.eqInt)(Data_Show.showInt);
var Nothing = /* #__PURE__ */ (function () {
    function Nothing() {

    };
    Nothing.value = new Nothing();
    return Nothing;
})();
var Just = /* #__PURE__ */ (function () {
    function Just(value0) {
        this.value0 = value0;
    };
    Just.create = function (value0) {
        return new Just(value0);
    };
    return Just;
})();
var weirdsum = function ($copy_accum) {
    return function ($copy_f1) {
        return function ($copy_n) {
            var $tco_var_accum = $copy_accum;
            var $tco_var_f1 = $copy_f1;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(accum, f1, n) {
                if (n === 0) {
                    $tco_done = true;
                    return accum;
                };
                var v = function (v1) {
                    $tco_var_accum = accum;
                    $tco_var_f1 = f1;
                    $copy_n = n - 1 | 0;
                    return;
                };
                var $17 = f1(n);
                if ($17 instanceof Just) {
                    $tco_var_accum = accum + $17.value0 | 0;
                    $tco_var_f1 = f1;
                    $copy_n = n - 1 | 0;
                    return;
                };
                return v(true);
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_accum, $tco_var_f1, $copy_n);
            };
            return $tco_result;
        };
    };
};
var tricksyinners = function ($copy_accum) {
    return function ($copy_x) {
        var $tco_var_accum = $copy_accum;
        var $tco_done = false;
        var $tco_result;
        function $tco_loop(accum, x) {
            var f$prime = function (y) {
                return y + 3 | 0;
            };
            if (x === 0) {
                $tco_done = true;
                return accum + (f$prime(x) * f$prime(x) | 0) | 0;
            };
            $tco_var_accum = accum + 2 | 0;
            $copy_x = x - 1 | 0;
            return;
        };
        while (!$tco_done) {
            $tco_result = $tco_loop($tco_var_accum, $copy_x);
        };
        return $tco_result;
    };
};
var g = function ($copy_x) {
    var $tco_done = false;
    var $tco_result;
    function $tco_loop(x) {
        if (x === 0) {
            $tco_done = true;
            return 0;
        };
        var v = function (v1) {
            $copy_x = x - 2 | 0;
            return;
        };
        var $22 = x === x;
        if ($22) {
            $copy_x = x - 1 | 0;
            return;
        };
        return v(true);
    };
    while (!$tco_done) {
        $tco_result = $tco_loop($copy_x);
    };
    return $tco_result;
};
var f = function ($copy_x) {
    var $tco_done = false;
    var $tco_result;
    function $tco_loop(x) {
        if (x === 0) {
            $tco_done = true;
            return 0;
        };
        var v = function (v1) {
            $copy_x = x - 2 | 0;
            return;
        };
        $copy_x = x - 1 | 0;
        return;
    };
    while (!$tco_done) {
        $tco_result = $tco_loop($copy_x);
    };
    return $tco_result;
};
var main = function __do() {
    assertEqual({
        expected: 0,
        actual: f(100000)
    })();
    assertEqual({
        expected: 0,
        actual: g(100000)
    })();
    assertEqual({
        expected: 20,
        actual: weirdsum(0)(function (x) {
            var $26 = x < 5;
            if ($26) {
                return new Just(2 * x | 0);
            };
            return Nothing.value;
        })(100000)
    })();
    assertEqual({
        expected: 200009,
        actual: tricksyinners(0)(100000)
    })();
    return Effect_Console.log("Done")();
};
export {
    Nothing,
    Just,
    f,
    g,
    weirdsum,
    tricksyinners,
    main
};
