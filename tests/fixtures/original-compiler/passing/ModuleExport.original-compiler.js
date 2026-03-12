import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var main = function __do() {
    Effect_Console.logShow(Data_Show.showString)(Data_Show.show(Data_Show.showNumber)(1.0))();
    return Effect_Console.log("Done")();
};
export {
    main
};
