import * as Data_Eq from "../Data.Eq/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var testTopLevel = function (n) {
    return n + 1.0;
};
var test = function (dictEq) {
    var eq = Data_Eq.eq(dictEq);
    return function (f) {
        return function (a) {
            var go = function ($copy_v) {
                return function ($copy_v1) {
                    var $tco_var_v = $copy_v;
                    var $tco_done = false;
                    var $tco_result;
                    function $tco_loop(v, v1) {
                        if (eq(v)(v1)) {
                            $tco_done = true;
                            return v;
                        };
                        $tco_var_v = f(v);
                        $copy_v1 = v;
                        return;
                    };
                    while (!$tco_done) {
                        $tco_result = $tco_loop($tco_var_v, $copy_v1);
                    };
                    return $tco_result;
                };
            };
            return go(f(a))(a);
        };
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    testTopLevel,
    test,
    main
};
