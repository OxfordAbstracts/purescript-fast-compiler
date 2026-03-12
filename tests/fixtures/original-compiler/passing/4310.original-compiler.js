import * as Effect_Console from "../Effect.Console/index.js";
import * as Lib from "../Lib/index.js";
var main = /* #__PURE__ */ (function () {
    var q = Lib.runTest(Lib["test$div$bslash"](Lib.testInt)(Lib.testInt))(new Lib.Tuple(4, 4));
    return Effect_Console.log("Done");
})();
export {
    main
};
