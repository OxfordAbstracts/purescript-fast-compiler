import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Safe_Coerce from "../Safe.Coerce/index.js";
var coerce = /* #__PURE__ */ Safe_Coerce.coerce();
var Pair = /* #__PURE__ */ (function () {
    function Pair(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Pair.create = function (value0) {
        return function (value1) {
            return new Pair(value0, value1);
        };
    };
    return Pair;
})();
var Multiplicative = function (x) {
    return x;
};
var wrap = function () {
    return coerce;
};
var wrap1 = /* #__PURE__ */ wrap();
var unwrap = function () {
    return coerce;
};
var unwrap1 = /* #__PURE__ */ unwrap();
var semiringMultiplicative = function (dictSemiring) {
    var mul = Data_Semiring.mul(dictSemiring);
    return {
        append: function (v) {
            return function (v1) {
                return mul(v)(v1);
            };
        }
    };
};
var newtypeMultiplicative = {
    Coercible0: function () {
        return undefined;
    }
};
var foldPair = function (dictSemigroup) {
    var append = Data_Semigroup.append(dictSemigroup);
    return function (f) {
        return function (v) {
            return append(f(v.value0))(f(v.value1));
        };
    };
};
var ala = function (dictFunctor) {
    var map = Data_Functor.map(dictFunctor);
    return function () {
        return function (v) {
            return function (f) {
                return map(unwrap1)(f(wrap1));
            };
        };
    };
};
var ala1 = /* #__PURE__ */ ala(Data_Functor.functorFn)();
var test = function (dictSemiring) {
    return ala1(Multiplicative)(foldPair(semiringMultiplicative(dictSemiring)));
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showInt)(test(Data_Semiring.semiringInt)(new Pair(2, 3)))();
    return Effect_Console.log("Done")();
};
var test1 = /* #__PURE__ */ (function () {
    return ala1(Multiplicative)(foldPair(semiringMultiplicative(Data_Semiring.semiringInt)))(new Pair(2, 3));
})();
export {
    wrap,
    unwrap,
    Multiplicative,
    Pair,
    foldPair,
    ala,
    test,
    test1,
    main,
    newtypeMultiplicative,
    semiringMultiplicative
};
