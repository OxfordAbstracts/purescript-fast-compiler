import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var shout = function (dictShow) {
    var $8 = Data_Show.show(dictShow);
    return function ($9) {
        return Effect_Console.log((function (v) {
            return v + "!";
        })($8($9)));
    };
};
var main = function __do() {
    shout(Data_Show.showString)("Test")();
    return Effect_Console.log("Done")();
};
export {
    shout,
    main
};
