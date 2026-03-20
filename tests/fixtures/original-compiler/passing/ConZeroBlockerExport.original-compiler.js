import * as ConZeroBlockerExport_DataModule from "../ConZeroBlockerExport.DataModule/index.js";
import * as ConZeroBlockerExport_Middle from "../ConZeroBlockerExport.Middle/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var test = /* #__PURE__ */ (function () {
    return ConZeroBlockerExport_Middle.event({
        name: "test",
        pt: new ConZeroBlockerExport_DataModule.PT("hello", 42)
    });
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    test,
    main
};
