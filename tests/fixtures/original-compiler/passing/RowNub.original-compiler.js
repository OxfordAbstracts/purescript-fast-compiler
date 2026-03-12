import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var nubUnion = function () {
    return function () {
        return function (v) {
            return function (v1) {
                return Type_Proxy["Proxy"].value;
            };
        };
    };
};
var test = /* #__PURE__ */ (function () {
    return nubUnion()()(Type_Proxy["Proxy"].value)(Type_Proxy["Proxy"].value);
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    nubUnion,
    test,
    main
};
