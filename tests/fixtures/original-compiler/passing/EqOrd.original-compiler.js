import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
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
var eqPair = function (dictEq) {
    var eq = Data_Eq.eq(dictEq);
    return function (dictEq1) {
        var eq1 = Data_Eq.eq(dictEq1);
        return {
            eq: function (v) {
                return function (v1) {
                    return eq(v.value0)(v1.value0) && eq1(v.value1)(v1.value1);
                };
            }
        };
    };
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showBoolean)(Data_Eq.eq(eqPair(Data_Eq.eqNumber)(Data_Eq.eqNumber))(new Pair(1.0, 2.0))(new Pair(1.0, 2.0)))();
    return Effect_Console.log("Done")();
};
var ordPair = function (dictOrd) {
    var compare = Data_Ord.compare(dictOrd);
    var eqPair1 = eqPair(dictOrd.Eq0());
    return function (dictOrd1) {
        var compare1 = Data_Ord.compare(dictOrd1);
        var eqPair2 = eqPair1(dictOrd1.Eq0());
        return {
            compare: function (v) {
                return function (v1) {
                    var v2 = compare(v.value0)(v1.value0);
                    if (v2 instanceof Data_Ordering.EQ) {
                        return compare1(v.value1)(v1.value1);
                    };
                    return v2;
                };
            },
            Eq0: function () {
                return eqPair2;
            }
        };
    };
};
export {
    Pair,
    main,
    ordPair,
    eqPair
};
