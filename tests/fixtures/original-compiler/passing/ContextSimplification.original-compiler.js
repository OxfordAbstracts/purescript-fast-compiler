import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var shout = function (dictShow) {
    var $13 = Data_Show.show(dictShow);
    return function ($14) {
        return Effect_Console.log((function (v) {
            return v + "!";
        })($13($14)));
    };
};
var usesShowTwice = function (dictShow) {
    var shout1 = shout(dictShow);
    var logShow = Effect_Console.logShow(dictShow);
    return function (v) {
        if (v) {
            return shout1;
        };
        if (!v) {
            return logShow;
        };
        throw new Error("Failed pattern match at Main (line 10, column 1 - line 10, column 27): " + [ v.constructor.name ]);
    };
};
var main = function __do() {
    usesShowTwice(Data_Show.showString)(true)("Test")();
    return Effect_Console.log("Done")();
};
export {
    shout,
    usesShowTwice,
    main
};
