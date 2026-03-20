import * as Control_Apply from "../Control.Apply/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
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
var outerVal = 42;
var main = /* #__PURE__ */ Effect_Console.log("Done");
var functorMaybe = {
    map: function (v) {
        return function (v1) {
            if (v1 instanceof Nothing) {
                return Nothing.value;
            };
            if (v1 instanceof Just) {
                return new Just(v(v1.value0));
            };
            throw new Error("Failed pattern match at Main (line 12, column 1 - line 14, column 30): " + [ v.constructor.name, v1.constructor.name ]);
        };
    }
};
var map = /* #__PURE__ */ Data_Functor.map(functorMaybe);
var test = /* #__PURE__ */ (function () {
    return map(function (v) {
        var y = v + 1 | 0;
        return v + y | 0;
    })(new Just(1));
})();
var applyMaybe = {
    apply: function (v) {
        return function (v1) {
            if (v instanceof Just && v1 instanceof Just) {
                return new Just(v.value0(v1.value0));
            };
            return Nothing.value;
        };
    },
    Functor0: function () {
        return functorMaybe;
    }
};
var testNoShadow = /* #__PURE__ */ (function () {
    return Control_Apply.apply(applyMaybe)(map(function (v) {
        return function (v1) {
            return {
                a: v,
                b: v1
            };
        };
    })(new Just(1)))(new Just(outerVal));
})();
export {
    Nothing,
    Just,
    test,
    outerVal,
    testNoShadow,
    main,
    functorMaybe,
    applyMaybe
};
