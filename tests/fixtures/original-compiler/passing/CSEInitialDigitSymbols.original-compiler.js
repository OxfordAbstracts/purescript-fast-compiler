import * as Data_Symbol from "../Data.Symbol/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var $$2$colon30IsSymbol = {
    reflectSymbol: function () {
        return "2:30";
    }
};
var $$2IsSymbol = {
    reflectSymbol: function () {
        return "2";
    }
};
var twoThirty = /* #__PURE__ */ (function () {
    return Data_Symbol.reflectSymbol($$2$colon30IsSymbol)(Type_Proxy["Proxy"].value);
})();
var two = /* #__PURE__ */ (function () {
    return Data_Symbol.reflectSymbol($$2IsSymbol)(Type_Proxy["Proxy"].value);
})();
var reflectSymbol$prime = function (dictIsSymbol) {
    return Data_Symbol.reflectSymbol(dictIsSymbol);
};
var two2 = /* #__PURE__ */ (function () {
    return reflectSymbol$prime($$2IsSymbol)(Type_Proxy["Proxy"].value);
})();
var twoThirty2 = /* #__PURE__ */ (function () {
    return reflectSymbol$prime($$2$colon30IsSymbol)(Type_Proxy["Proxy"].value);
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    reflectSymbol$prime,
    two,
    two2,
    twoThirty,
    twoThirty2,
    main
};
