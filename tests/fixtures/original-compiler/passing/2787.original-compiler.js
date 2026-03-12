import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ (function () {
    if (Data_Ord.between(Data_Ord.ordInt)(0)(1)(2)) {
        return Effect_Console.log("Fail");
    };
    if (Data_Boolean.otherwise) {
        return Effect_Console.log("Done");
    };
    throw new Error("Failed pattern match at Main (line 6, column 1 - line 8, column 27): " + [  ]);
})();
export {
    main
};
