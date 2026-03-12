import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var lacksX = function () {
    return function (v) {
        return Type_Proxy["Proxy"].value;
    };
};
var lacksX1 = /* #__PURE__ */ lacksX();
var test1 = /* #__PURE__ */ (function () {
    return lacksX1(Type_Proxy["Proxy"].value);
})();
var test2 = function () {
    return function (v) {
        return lacksX1(Type_Proxy["Proxy"].value);
    };
};
var test3 = /* #__PURE__ */ (function () {
    return test2()(Type_Proxy["Proxy"].value);
})();
var lacksSym = function () {
    return function (v) {
        return Type_Proxy["Proxy"].value;
    };
};
var test4 = /* #__PURE__ */ lacksSym();
export {
    lacksX,
    lacksSym,
    test1,
    test2,
    test3,
    test4,
    main
};
