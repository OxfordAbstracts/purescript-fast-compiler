import * as Effect_Console from "../Effect.Console/index.js";
import * as Lib from "../Lib/index.js";
var test = /* #__PURE__ */ (function () {
    return new Lib.TA(42, true);
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    test,
    main
};
