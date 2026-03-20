import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var Product = /* #__PURE__ */ (function () {
    function Product(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Product.create = function (value0) {
        return function (value1) {
            return new Product(value0, value1);
        };
    };
    return Product;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var eqMu = function (dictEq) {
    var eq = Data_Eq.eq(dictEq);
    return function (dictEq1) {
        var eq1 = Data_Eq.eq(dictEq1);
        return {
            eq: function (x) {
                return function (y) {
                    return eq(x.value0)(y.value0) && eq1(x.value1)(y.value1);
                };
            }
        };
    };
};
var ordMu = function (dictOrd) {
    var compare = Data_Ord.compare(dictOrd);
    var eqMu1 = eqMu(dictOrd.Eq0());
    return function (dictOrd1) {
        var compare1 = Data_Ord.compare(dictOrd1);
        var eqMu2 = eqMu1(dictOrd1.Eq0());
        return {
            compare: function (x) {
                return function (y) {
                    var v = compare(x.value0)(y.value0);
                    if (v instanceof Data_Ordering.LT) {
                        return Data_Ordering.LT.value;
                    };
                    if (v instanceof Data_Ordering.GT) {
                        return Data_Ordering.GT.value;
                    };
                    return compare1(x.value1)(y.value1);
                };
            },
            Eq0: function () {
                return eqMu2;
            }
        };
    };
};
var eq1Mu = function (dictEq) {
    var eqMu1 = eqMu(dictEq);
    return {
        eq1: function (dictEq1) {
            return Data_Eq.eq(eqMu1(dictEq1));
        }
    };
};
var ord1Mu = function (dictOrd) {
    var ordMu1 = ordMu(dictOrd);
    var eq1Mu1 = eq1Mu(dictOrd.Eq0());
    return {
        compare1: function (dictOrd1) {
            return Data_Ord.compare(ordMu1(dictOrd1));
        },
        Eq10: function () {
            return eq1Mu1;
        }
    };
};
export {
    Product,
    main,
    eqMu,
    eq1Mu,
    ordMu,
    ord1Mu
};
