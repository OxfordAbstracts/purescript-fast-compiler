import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Symbol from "../Data.Symbol/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Data_Symbol from "../Type.Data.Symbol/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var append = /* #__PURE__ */ Type_Data_Symbol.append();
var when = /* #__PURE__ */ Control_Applicative.when(Effect.applicativeEffect);
var symB = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var symA = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var sym = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var egBA = /* #__PURE__ */ append(symB)(symA);
var egAB = /* #__PURE__ */ append(symA)(symB);
var egA$prime = /* #__PURE__ */ append(sym)(/* #__PURE__ */ append(symA)(sym));
var main = /* #__PURE__ */ (function () {
    var gotBA = Data_Symbol.reflectSymbol({
        reflectSymbol: function () {
            return "BA";
        }
    })(egBA) === "BA";
    var gotAB = Data_Symbol.reflectSymbol({
        reflectSymbol: function () {
            return "AB";
        }
    })(egAB) === "AB";
    var gotA$prime = Data_Symbol.reflectSymbol({
        reflectSymbol: function () {
            return "A";
        }
    })(egA$prime) === "A";
    return function __do() {
        when(!gotAB)(Effect_Console.log("Did not get AB"))();
        when(!gotBA)(Effect_Console.log("Did not get BA"))();
        when(!gotA$prime)(Effect_Console.log("Did not get A"))();
        return when(gotAB && (gotBA && gotA$prime))(Effect_Console.log("Done"))();
    };
})();
export {
    sym,
    symA,
    symB,
    egAB,
    egBA,
    egA$prime,
    main
};
