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
var L = /* #__PURE__ */ (function () {
    function L(value0) {
        this.value0 = value0;
    };
    L.create = function (value0) {
        return new L(value0);
    };
    return L;
})();
var R = /* #__PURE__ */ (function () {
    function R(value0) {
        this.value0 = value0;
    };
    R.create = function (value0) {
        return new R(value0);
    };
    return R;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var lefts = /* #__PURE__ */ (function () {
    var go = function ($copy_v) {
        return function ($copy_v1) {
            var $tco_var_v = $copy_v;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(v, v1) {
                if (v1 instanceof N) {
                    $tco_done = true;
                    return v;
                };
                if (v1 instanceof C && v1.value0 instanceof L) {
                    $tco_var_v = new C(v1.value0.value0, v);
                    $copy_v1 = v1.value1;
                    return;
                };
                if (v1 instanceof C) {
                    $tco_var_v = v;
                    $copy_v1 = v1.value1;
                    return;
                };
                throw new Error("Failed pattern match at Main (line 13, column 3 - line 13, column 44): " + [ v.constructor.name, v1.constructor.name ]);
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_v, $copy_v1);
            };
            return $tco_result;
        };
    };
    return go(N.value);
})();
export {
    L,
    R,
    C,
    N,
    lefts,
    main
};
