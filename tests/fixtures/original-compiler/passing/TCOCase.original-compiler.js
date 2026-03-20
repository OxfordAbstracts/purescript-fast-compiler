import * as Effect_Console from "../Effect.Console/index.js";
var One = /* #__PURE__ */ (function () {
    function One() {

    };
    One.value = new One();
    return One;
})();
var More = /* #__PURE__ */ (function () {
    function More(value0) {
        this.value0 = value0;
    };
    More.create = function (value0) {
        return new More(value0);
    };
    return More;
})();
var main = /* #__PURE__ */ (function () {
    var to = function ($copy_v) {
        return function ($copy_v1) {
            var $tco_var_v = $copy_v;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(v, v1) {
                if (v === 0.0) {
                    $tco_done = true;
                    return v1;
                };
                $tco_var_v = v - 1.0;
                $copy_v1 = new More(v1);
                return;
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_v, $copy_v1);
            };
            return $tco_result;
        };
    };
    var from = function ($copy_v) {
        var $tco_done1 = false;
        var $tco_result;
        function $tco_loop(v) {
            if (v instanceof One) {
                $tco_done1 = true;
                return "Done";
            };
            if (v instanceof More) {
                $copy_v = v.value0;
                return;
            };
            throw new Error("Failed pattern match at Main (line 12, column 3 - line 12, column 20): " + [ v.constructor.name ]);
        };
        while (!$tco_done1) {
            $tco_result = $tco_loop($copy_v);
        };
        return $tco_result;
    };
    return Effect_Console.log(from(to(10000.0)(One.value)));
})();
export {
    One,
    More,
    main
};
