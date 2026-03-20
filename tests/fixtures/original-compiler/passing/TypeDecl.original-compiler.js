import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var k = function (x) {
    return function (y) {
        return x;
    };
};
var iterate = function ($copy_v) {
    return function ($copy_v1) {
        return function ($copy_v2) {
            var $tco_var_v = $copy_v;
            var $tco_var_v1 = $copy_v1;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(v, v1, v2) {
                if (v === 0.0) {
                    $tco_done = true;
                    return v2;
                };
                $tco_var_v = v - 1.0;
                $tco_var_v1 = v1;
                $copy_v2 = v1(v2);
                return;
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_v, $tco_var_v1, $copy_v2);
            };
            return $tco_result;
        };
    };
};
export {
    k,
    iterate,
    main
};
