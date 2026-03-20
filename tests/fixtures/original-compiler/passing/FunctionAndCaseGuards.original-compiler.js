import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var test = function (a) {
    if (false) {
        if (false && a > 0) {
            return true;
        };
        return true;
    };
    if (Data_Boolean.otherwise) {
        return true;
    };
    throw new Error("Failed pattern match at Main (line 9, column 1 - line 9, column 23): " + [ a.constructor.name ]);
};
var main = /* #__PURE__ */ (function () {
    var $4 = test(0);
    if ($4) {
        return Effect_Console.log("Done");
    };
    return Control_Applicative.pure(Effect.applicativeEffect)(Data_Unit.unit);
})();
export {
    test,
    main
};
