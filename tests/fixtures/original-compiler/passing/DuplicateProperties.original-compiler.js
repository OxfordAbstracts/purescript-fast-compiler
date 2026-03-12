import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var subtractX = function (v) {
    return Type_Proxy["Proxy"].value;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var hasX = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var test1 = /* #__PURE__ */ subtractX(/* #__PURE__ */ subtractX(hasX));
var extractX = function (v) {
    return Type_Proxy["Proxy"].value;
};
var test2 = function (x) {
    return extractX(subtractX(subtractX(x)));
};
export {
    subtractX,
    extractX,
    hasX,
    test1,
    test2,
    main
};
