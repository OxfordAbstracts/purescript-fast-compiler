import * as Data_Eq from "../Data.Eq/index.js";
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
export {
    In,
    main,
    eqMu
};
