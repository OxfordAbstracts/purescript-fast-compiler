import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as SolvingIsSymbol_Lib from "../SolvingIsSymbol.Lib/index.js";
var main = /* #__PURE__ */ (function () {
    var lit = SolvingIsSymbol_Lib.libReflectSymbol({
        reflectSymbol: function () {
            return "literal";
        }
    })(SolvingIsSymbol_Lib.literalSymbol);
    return Control_Applicative.when(Effect.applicativeEffect)(lit === "literal")(Effect_Console.log("Done"));
})();
export {
    main
};
