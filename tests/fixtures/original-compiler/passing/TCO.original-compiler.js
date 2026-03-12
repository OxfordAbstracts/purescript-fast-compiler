import * as Control_Category from "../Control.Category/index.js";
import * as Control_Monad_Rec_Class from "../Control.Monad.Rec.Class/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var logShow = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showInt);
var applyN = /* #__PURE__ */ (function () {
    var go = function ($copy_v) {
        return function ($copy_v1) {
            return function ($copy_v2) {
                var $tco_var_v = $copy_v;
                var $tco_var_v1 = $copy_v1;
                var $tco_done = false;
                var $tco_result;
                function $tco_loop(v, v1, v2) {
                    if (v1 <= 0) {
                        $tco_done = true;
                        return v;
                    };
                    $tco_var_v = function ($17) {
                        return v2(v($17));
                    };
                    $tco_var_v1 = v1 - 1 | 0;
                    $copy_v2 = v2;
                    return;
                };
                while (!$tco_done) {
                    $tco_result = $tco_loop($tco_var_v, $tco_var_v1, $copy_v2);
                };
                return $tco_result;
            };
        };
    };
    return go(Control_Category.identity(Control_Category.categoryFn));
})();
var main = /* #__PURE__ */ (function () {
    var f = function (x) {
        return x + 1 | 0;
    };
    return function __do() {
        logShow(applyN(0)(f)(0))();
        logShow(applyN(1)(f)(0))();
        logShow(applyN(2)(f)(0))();
        logShow(applyN(3)(f)(0))();
        logShow(applyN(4)(f)(0))();
        var largeArray = Data_Array.range(1)(10000);
        logShow(Data_Array.length((Data_Array.span(function (v1) {
            return true;
        })(largeArray)).init))();
        logShow(Control_Monad_Rec_Class.tailRec(function (n) {
            var $16 = n < 10000;
            if ($16) {
                return new Control_Monad_Rec_Class.Loop(n + 1 | 0);
            };
            return new Control_Monad_Rec_Class.Done(42);
        })(0))();
        return Effect_Console.log("Done")();
    };
})();
export {
    main,
    applyN
};
