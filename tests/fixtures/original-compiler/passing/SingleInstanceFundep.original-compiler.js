import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var singleInstanceFundepRow = /* #__PURE__ */ (function () {
    return {
        unified: Type_Proxy["Proxy"].value
    };
})();
var unified = function (dict) {
    return dict.unified;
};
var test = /* #__PURE__ */ unified(singleInstanceFundepRow);
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    unified,
    test,
    main,
    singleInstanceFundepRow
};
