import * as Data_Array from "../Data.Array/index.js";
import * as Data_Array_Partial from "../Data.Array.Partial/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var tail = /* #__PURE__ */ Data_Array_Partial.tail();
var length = /* #__PURE__ */ (function () {
    var go = function ($copy_acc) {
        return function ($copy_arr) {
            var $tco_var_acc = $copy_acc;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(acc, arr) {
                var $5 = Data_Array["null"](arr);
                if ($5) {
                    $tco_done = true;
                    return acc;
                };
                $tco_var_acc = acc + 1 | 0;
                $copy_arr = tail(arr);
                return;
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_acc, $copy_arr);
            };
            return $tco_result;
        };
    };
    return go(0);
})();
var main = function __do() {
    Effect_Console.logShow(Data_Show.showInt)(length(Data_Array.range(1)(10000)))();
    return Effect_Console.log("Done")();
};
export {
    length,
    main
};
