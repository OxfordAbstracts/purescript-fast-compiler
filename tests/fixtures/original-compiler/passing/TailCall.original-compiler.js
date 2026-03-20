import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var C = /* #__PURE__ */ (function () {
    function C(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    C.create = function (value0) {
        return function (value1) {
            return new C(value0, value1);
        };
    };
    return C;
})();
var N = /* #__PURE__ */ (function () {
    function N() {

    };
    N.value = new N();
    return N;
})();
var test = function ($copy_v) {
    return function ($copy_v1) {
        var $tco_var_v = $copy_v;
        var $tco_done = false;
        var $tco_result;
        function $tco_loop(v, v1) {
            if (v1 instanceof N) {
                $tco_done = true;
                return v;
            };
            if (v1 instanceof C) {
                $tco_var_v = v + v1.value0;
                $copy_v1 = v1.value1;
                return;
            };
            throw new Error("Failed pattern match at Main (line 8, column 1 - line 8, column 37): " + [ v.constructor.name, v1.constructor.name ]);
        };
        while (!$tco_done) {
            $tco_result = $tco_loop($tco_var_v, $copy_v1);
        };
        return $tco_result;
    };
};
var notATailCall = function (x) {
    return (function (notATailCall1) {
        return notATailCall1(x);
    })(function (x1) {
        return x1;
    });
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showNumber)(test(0.0)(new C(1.0, new C(2.0, new C(3.0, N.value)))))();
    return Effect_Console.log("Done")();
};
var loop = function ($copy_x) {
    var $tco_result;
    function $tco_loop(x) {
        $copy_x = x + 1.0;
        return;
    };
    while (!false) {
        $tco_result = $tco_loop($copy_x);
    };
    return $tco_result;
};
export {
    C,
    N,
    test,
    loop,
    notATailCall,
    main
};
