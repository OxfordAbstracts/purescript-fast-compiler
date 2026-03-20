import * as Control_Apply from "../Control.Apply/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var Const = function (x) {
    return x;
};
var runConst = function (v) {
    return v;
};
var functorConst = {
    map: function (v) {
        return function (v1) {
            return v1;
        };
    }
};
var example1 = /* #__PURE__ */ (function () {
    var discard1 = function (x) {
        return function (f) {
            return x + f(Data_Unit.unit);
        };
    };
    return discard1("Do")(function () {
        return discard1(" notation")(function () {
            return discard1(" for")(function () {
                return " Semigroup";
            });
        });
    });
})();
var applySecond = function (dictApply) {
    var apply = Control_Apply.apply(dictApply);
    var map = Data_Functor.map(dictApply.Functor0());
    return function (fa) {
        return function (fb) {
            return apply(map(Data_Function["const"](identity))(fa))(fb);
        };
    };
};
var applyConst = function (dictSemigroup) {
    var append1 = Data_Semigroup.append(dictSemigroup);
    return {
        apply: function (v) {
            return function (v1) {
                return append1(v)(v1);
            };
        },
        Functor0: function () {
            return functorConst;
        }
    };
};
var applySecond1 = /* #__PURE__ */ applySecond(/* #__PURE__ */ applyConst(Data_Semigroup.semigroupString));
var example2 = /* #__PURE__ */ (function () {
    var discard1 = function (x) {
        return function (f) {
            return applySecond1(x)(f(Data_Unit.unit));
        };
    };
    return discard1("Do")(function () {
        return discard1(" notation")(function () {
            return discard1(" for")(function () {
                return " Apply";
            });
        });
    });
})();
var main = function __do() {
    Effect_Console.log(example1)();
    Effect_Console.log(runConst(example2))();
    return Effect_Console.log("Done")();
};
export {
    example1,
    applySecond,
    Const,
    runConst,
    example2,
    main,
    functorConst,
    applyConst
};
