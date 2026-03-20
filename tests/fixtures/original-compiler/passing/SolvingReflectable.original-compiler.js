import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Reflectable from "../Data.Reflectable/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var eq = /* #__PURE__ */ Data_Eq.eq(Data_Ordering.eqOrdering);
var refString = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var refStringPass = /* #__PURE__ */ (function () {
    return Data_Reflectable.reflectType({
        reflectType: function () {
            return "PureScript";
        }
    })(refString) === "PureScript";
})();
var refOrderingLT = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var refOrderingGT = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var refOrderingEQ = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var refOrderingPass = /* #__PURE__ */ (function () {
    return eq(Data_Reflectable.reflectType({
        reflectType: function () {
            return Data_Ordering.LT.value;
        }
    })(refOrderingLT))(Data_Ordering.LT.value) && (eq(Data_Reflectable.reflectType({
        reflectType: function () {
            return Data_Ordering.EQ.value;
        }
    })(refOrderingEQ))(Data_Ordering.EQ.value) && eq(Data_Reflectable.reflectType({
        reflectType: function () {
            return Data_Ordering.GT.value;
        }
    })(refOrderingGT))(Data_Ordering.GT.value));
})();
var refInt = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var refIntPass = /* #__PURE__ */ (function () {
    return Data_Reflectable.reflectType({
        reflectType: function () {
            return 42;
        }
    })(refInt) === 42;
})();
var refBooleanT = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var refBooleanF = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var refBooleanPass = /* #__PURE__ */ (function () {
    return Data_Reflectable.reflectType({
        reflectType: function () {
            return true;
        }
    })(refBooleanT) === true && Data_Reflectable.reflectType({
        reflectType: function () {
            return false;
        }
    })(refBooleanF) === false;
})();
var main = /* #__PURE__ */ (function () {
    return Control_Applicative.when(Effect.applicativeEffect)(refIntPass && (refStringPass && (refBooleanPass && refOrderingPass)))(Effect_Console.log("Done"));
})();
export {
    refInt,
    refIntPass,
    refString,
    refStringPass,
    refBooleanT,
    refBooleanF,
    refBooleanPass,
    refOrderingLT,
    refOrderingEQ,
    refOrderingGT,
    refOrderingPass,
    main
};
