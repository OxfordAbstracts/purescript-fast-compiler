import * as Data_Function from "../Data.Function/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var main = function __do() {
    Effect_Console.logShow(Data_Show.showUnit)(Data_Function["const"](Data_Unit.unit)("Hello world"))();
    return Effect_Console.log("Done")();
};
export {
    main
};
