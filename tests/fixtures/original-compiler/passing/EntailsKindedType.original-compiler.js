import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var when = /* #__PURE__ */ Control_Applicative.when(Effect.applicativeEffect);
var test = function (dictShow) {
    var show = Data_Show.show(dictShow);
    return function (x) {
        return show(x);
    };
};
var test1 = /* #__PURE__ */ test(Data_Show.showUnit);
var main = function __do() {
    when(Data_Show.show(Data_Show.showUnit)(Data_Unit.unit) === "unit")(Effect_Console.log("Done"))();
    return when(test1(Data_Unit.unit) === "unit")(Effect_Console.log("Done"))();
};
export {
    test,
    main
};
