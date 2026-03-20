import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Data_Ordering from "../Type.Data.Ordering/index.js";
import * as Type_Data_Symbol from "../Type.Data.Symbol/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var compare = /* #__PURE__ */ Type_Data_Symbol.compare();
var eq = /* #__PURE__ */ Data_Eq.eq(Data_Ordering.eqOrdering);
var when = /* #__PURE__ */ Control_Applicative.when(Effect.applicativeEffect);
var symB = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var symA = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var egLT = /* #__PURE__ */ compare(symA)(symB);
var egGT = /* #__PURE__ */ compare(symB)(symA);
var egEQ = /* #__PURE__ */ compare(symA)(symA);
var main = /* #__PURE__ */ (function () {
    var gotLT = eq(Type_Data_Ordering.reflectOrdering(Type_Data_Ordering.isOrderingLT)(egLT))(Data_Ordering.LT.value);
    var gotGT = eq(Type_Data_Ordering.reflectOrdering(Type_Data_Ordering.isOrderingGT)(egGT))(Data_Ordering.GT.value);
    var gotEQ = eq(Type_Data_Ordering.reflectOrdering(Type_Data_Ordering.isOrderingEQ)(egEQ))(Data_Ordering.EQ.value);
    return function __do() {
        when(!gotLT)(Effect_Console.log("Did not get LT"))();
        when(!gotEQ)(Effect_Console.log("Did not get EQ"))();
        when(!gotGT)(Effect_Console.log("Did not get GT"))();
        return when(gotLT && (gotEQ && gotGT))(Effect_Console.log("Done"))();
    };
})();
export {
    symA,
    symB,
    egLT,
    egEQ,
    egGT,
    main
};
