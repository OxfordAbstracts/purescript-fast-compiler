import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var f = function (x) {
    return function (y) {
        var g = (function () {
            if (y === 0.0) {
                return x;
            };
            return 1.0 + y * y;
        })();
        return g + x + y;
    };
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showNumber)(f(1.0)(10.0))();
    return Effect_Console.log("Done")();
};
export {
    f,
    main
};
