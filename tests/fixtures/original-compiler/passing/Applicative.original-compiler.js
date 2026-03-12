import * as Effect_Console from "../Effect.Console/index.js";
var Nothing = /* #__PURE__ */ (function () {
    function Nothing() {

    };
    Nothing.value = new Nothing();
    return Nothing;
})();
var Just = /* #__PURE__ */ (function () {
    function Just(value0) {
        this.value0 = value0;
    };
    Just.create = function (value0) {
        return new Just(value0);
    };
    return Just;
})();
var pure = function (dict) {
    return dict.pure;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var apply = function (dict) {
    return dict.apply;
};
var applicativeMaybe = /* #__PURE__ */ (function () {
    return {
        pure: Just.create,
        apply: function (v) {
            return function (v1) {
                if (v instanceof Just && v1 instanceof Just) {
                    return new Just(v.value0(v1.value0));
                };
                return Nothing.value;
            };
        }
    };
})();
export {
    apply,
    pure,
    Nothing,
    Just,
    main,
    applicativeMaybe
};
