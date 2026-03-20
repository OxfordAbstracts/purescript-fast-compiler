import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Middle from "../Middle/index.js";
import * as Test from "../Test/index.js";
var main = function __do() {
    Effect_Console.logShow(Data_Show.showUnit)(Middle.middle(Test.unitTestCls)(Data_Unit.unit))();
    return Effect_Console.log("Done")();
};
export {
    main
};
