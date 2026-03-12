import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var balanced2 = function () {
    return function () {
        return function () {
            return {};
        };
    };
};
var balanced1 = {};
var balanced = function () {
    return function (v) {
        return "ok";
    };
};
var balanced3 = /* #__PURE__ */ balanced();
var b3 = /* #__PURE__ */ (function () {
    return balanced3(Type_Proxy["Proxy"].value);
})();
var b2 = /* #__PURE__ */ (function () {
    return balanced3(Type_Proxy["Proxy"].value);
})();
var b1 = /* #__PURE__ */ (function () {
    return balanced3(Type_Proxy["Proxy"].value);
})();
var b0 = /* #__PURE__ */ (function () {
    return balanced3(Type_Proxy["Proxy"].value);
})();
var main = function __do() {
    Effect_Console.log(b0)();
    Effect_Console.log(b1)();
    Effect_Console.log(b2)();
    Effect_Console.log(b3)();
    return Effect_Console.log("Done")();
};
export {
    balanced,
    b0,
    b1,
    b2,
    b3,
    main,
    balanced1,
    balanced2
};
