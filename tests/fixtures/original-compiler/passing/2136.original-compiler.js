import * as Data_Bounded from "../Data.Bounded/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ (function () {
    var $4 = (-Data_Bounded.bottom(Data_Bounded.boundedInt) | 0) > Data_Bounded.top(Data_Bounded.boundedInt);
    if ($4) {
        return Effect_Console.log("Fail");
    };
    return Effect_Console.log("Done");
})();
export {
    main
};
