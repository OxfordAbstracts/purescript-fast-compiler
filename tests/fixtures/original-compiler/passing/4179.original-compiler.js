import * as $foreign from "./foreign.js";
import * as Control_Category from "../Control.Category/index.js";
import * as CustomAssert from "../CustomAssert/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var $runtime_lazy = function (name, moduleName, init) {
    var state = 0;
    var val;
    return function (lineNumber) {
        if (state === 2) return val;
        if (state === 1) throw new ReferenceError(name + " was needed before it finished initializing (module " + moduleName + ", line " + lineNumber + ")", moduleName, lineNumber);
        state = 1;
        val = init();
        state = 2;
        return val;
    };
};
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var assertEqual = /* #__PURE__ */ Test_Assert.assertEqual(Data_Eq.eqString)(Data_Show.showString);
var assertEqual1 = /* #__PURE__ */ Test_Assert.assertEqual(Data_Eq.eqInt)(Data_Show.showInt);
var assertEqual2 = /* #__PURE__ */ Test_Assert.assertEqual(/* #__PURE__ */ Data_Maybe.eqMaybe(Data_Eq.eqString))(/* #__PURE__ */ Data_Maybe.showMaybe(Data_Show.showString));
var runtimeImport = /* #__PURE__ */ (function () {
    return $foreign.runtimeImportImpl(Data_Maybe.Nothing.value)(Data_Maybe.Just.create);
})();
var force = function (f) {
    return f(Data_Unit.unit);
};
var complicatedIdentity = /* #__PURE__ */ (function () {
    var f = function (n) {
        return {
            tick: (function () {
                var $20 = n <= 0;
                if ($20) {
                    return identity;
                };
                return (f(n - 1 | 0)).tock(identity);
            })(),
            tock: function (a) {
                return $lazy_g(33)(n)(a);
            }
        };
    };
    var $lazy_h = $runtime_lazy("h", "Main", function () {
        return (f(10)).tick;
    });
    var $lazy_g = $runtime_lazy("g", "Main", function () {
        return function (n) {
            return (f(n)).tick;
        };
    });
    var h = $lazy_h(38);
    var g = $lazy_g(35);
    return h;
})();
var alpha = {
    backref: function (v) {
        return $lazy_bravo(14);
    },
    x: 1
};
var $lazy_bravo = /* #__PURE__ */ $runtime_lazy("bravo", "Main", function () {
    return force(function (v) {
        return alpha.x;
    });
});
var bravo = /* #__PURE__ */ $lazy_bravo(15);
var main = function __do() {
    var err = CustomAssert.assertThrows(function (v) {
        var $lazy_selfOwn = $runtime_lazy("selfOwn", "Main", function () {
            return {
                a: 1,
                b: force(function (v1) {
                    return ($lazy_selfOwn(52)).a;
                })
            };
        });
        var selfOwn = $lazy_selfOwn(52);
        return selfOwn;
    })();
    assertEqual({
        actual: err,
        expected: "ReferenceError: selfOwn was needed before it finished initializing (module Main, line 52)"
    })();
    var err2 = CustomAssert.assertThrows(function (v) {
        var j = function (x) {
            return function (y) {
                return function (z) {
                    return {
                        left: x(y)(z),
                        right: ($lazy_f(66)).left
                    };
                };
            };
        };
        var h = function (x) {
            return j(x)(x);
        };
        var g = function (x) {
            return (j(x)(x)(x)).right;
        };
        var $lazy_f = $runtime_lazy("f", "Main", function () {
            return {
                left: g(identity),
                right: h(identity)
            };
        });
        var f = $lazy_f(58);
        return f;
    })();
    assertEqual({
        actual: err2,
        expected: "ReferenceError: f was needed before it finished initializing (module Main, line 66)"
    })();
    assertEqual1({
        actual: bravo,
        expected: 1
    })();
    return runtimeImport("InitializationError")(function (err3) {
        return function __do() {
            assertEqual2({
                actual: err3,
                expected: new Data_Maybe.Just("ReferenceError: alphaArray was needed before it finished initializing (module InitializationError, line 0)")
            })();
            return Effect_Console.log("Done")();
        };
    })();
};
export {
    runtimeImportImpl
} from "./foreign.js";
export {
    force,
    alpha,
    bravo,
    complicatedIdentity,
    runtimeImport,
    main
};
