import * as DataModule from "../DataModule/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var usePT = function (pt) {
    return DataModule.showPT(pt);
};
var mkTalk = /* #__PURE__ */ (function () {
    return DataModule.Talk.value;
})();
var mkAlias = {
    name: "test",
    code: 1
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    usePT,
    mkTalk,
    mkAlias,
    main
};
