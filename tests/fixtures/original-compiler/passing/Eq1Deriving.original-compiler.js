import * as Data_Eq from "../Data.Eq/index.js";
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
var eq1Mu = function (dictEq) {
    var eqMu1 = eqMu(dictEq);
    return {
        eq1: function (dictEq1) {
            return Data_Eq.eq(eqMu1(dictEq1));
        }
    };
};
export {
    Product,
    main,
    eqMu,
    eq1Mu
};
