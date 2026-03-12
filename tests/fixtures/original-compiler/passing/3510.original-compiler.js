import * as Effect_Console from "../Effect.Console/index.js";
var Just = /* #__PURE__ */ (function () {
    function Just(value0) {
        this.value0 = value0;
    };
    Just.create = function (value0) {
        return new Just(value0);
    };
    return Just;
})();
var Nothing = /* #__PURE__ */ (function () {
    function Nothing() {

    };
    Nothing.value = new Nothing();
    return Nothing;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var eqT = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Just && y instanceof Just) {
                return x.value0 === y.value0;
            };
            if (x instanceof Nothing && y instanceof Nothing) {
                return true;
            };
            return false;
        };
    }
};
export {
    Just,
    Nothing,
    main,
    eqT
};
