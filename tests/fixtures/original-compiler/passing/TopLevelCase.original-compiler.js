import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingNumber);
var A = /* #__PURE__ */ (function () {
    function A() {

    };
    A.value = new A();
    return A;
})();
var parseTest = function (dictPartial) {
    return function (v) {
        return function (v1) {
            if (v1 === 0.0) {
                return 0.0;
            };
            throw new Error("Failed pattern match at Main (line 17, column 1 - line 17, column 22): " + [ v.constructor.name, v1.constructor.name ]);
        };
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var guardsTest = function (v) {
    if (v.length === 1 && v[0] > 0.0) {
        return [  ];
    };
    return v;
};
var gcd = function ($copy_v) {
    return function ($copy_v1) {
        var $tco_var_v = $copy_v;
        var $tco_done = false;
        var $tco_result;
        function $tco_loop(v, v1) {
            if (v === 0.0) {
                $tco_done = true;
                return v1;
            };
            if (v1 === 0.0) {
                $tco_done = true;
                return v;
            };
            if (v > v1) {
                $tco_var_v = mod(v)(v1);
                $copy_v1 = v1;
                return;
            };
            $tco_var_v = mod(v1)(v);
            $copy_v1 = v;
            return;
        };
        while (!$tco_done) {
            $tco_result = $tco_loop($tco_var_v, $copy_v1);
        };
        return $tco_result;
    };
};
export {
    gcd,
    guardsTest,
    A,
    parseTest,
    main
};
