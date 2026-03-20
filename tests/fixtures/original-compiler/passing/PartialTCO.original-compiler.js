import * as Effect_Console from "../Effect.Console/index.js";
var partialTCO = function () {
    return function ($copy_v) {
        return function ($copy_v1) {
            var $tco_var_v = $copy_v;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(v, v1) {
                if (v && v1 === 0) {
                    $tco_done = true;
                    return 0;
                };
                if (v) {
                    $tco_var_v = true;
                    $copy_v1 = v1 - 1 | 0;
                    return;
                };
                throw new Error("Failed pattern match at Main (line 11, column 1 - line 11, column 47): " + [ v.constructor.name, v1.constructor.name ]);
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_v, $copy_v1);
            };
            return $tco_result;
        };
    };
};
var partialTCO1 = /* #__PURE__ */ partialTCO();
var main = /* #__PURE__ */ (function () {
    var v = partialTCO1(true)(1000000);
    return Effect_Console.log("Done");
})();
export {
    main,
    partialTCO
};
