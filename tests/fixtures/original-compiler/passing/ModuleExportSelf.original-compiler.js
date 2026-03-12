import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var bar = true;
var main = function __do() {
    Effect_Console.logShow(Data_Show.showString)(Data_Show.show(Data_Show.showBoolean)(bar))();
    return Effect_Console.log("Done")();
};
export {
    bar,
    main
};
