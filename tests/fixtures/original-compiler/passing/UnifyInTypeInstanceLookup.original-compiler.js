import * as Effect_Console from "../Effect.Console/index.js";
var Z = /* #__PURE__ */ (function () {
    function Z() {

    };
    Z.value = new Z();
    return Z;
})();
var S = /* #__PURE__ */ (function () {
    function S(value0) {
        this.value0 = value0;
    };
    S.create = function (value0) {
        return new S(value0);
    };
    return S;
})();
var test = function () {
    return function (a) {
        return function (v) {
            return a;
        };
    };
};
var spin = function ($copy_a) {
    var $tco_result;
    function $tco_loop(a) {
        $copy_a = a;
        return;
    };
    while (!false) {
        $tco_result = $tco_loop($copy_a);
    };
    return $tco_result;
};
var test1 = function (dictEQ) {
    return test(dictEQ)(spin(1))(new S(Z.value));
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var eqT = {};
var eqF = {};
export {
    Z,
    S,
    test,
    spin,
    test1,
    main,
    eqT,
    eqF
};
