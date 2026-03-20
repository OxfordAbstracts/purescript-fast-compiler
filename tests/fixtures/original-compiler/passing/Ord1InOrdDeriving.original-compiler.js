import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var In = function (x) {
    return x;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var eqMu = function (dictEq1) {
    var eq1 = Data_Eq.eq1(dictEq1);
    return {
        eq: function (x) {
            return function (y) {
                return eq1(eqMu(dictEq1))(x)(y);
            };
        }
    };
};
var ordMu = function (dictOrd1) {
    var compare1 = Data_Ord.compare1(dictOrd1);
    var eqMu1 = eqMu(dictOrd1.Eq10());
    return {
        compare: function (x) {
            return function (y) {
                return compare1(ordMu(dictOrd1))(x)(y);
            };
        },
        Eq0: function () {
            return eqMu1;
        }
    };
};
export {
    In,
    main,
    eqMu,
    ordMu
};
