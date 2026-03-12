import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var test = /* #__PURE__ */ (function () {
    var g = function (v) {
        if (v === 0.0) {
            return true;
        };
        return f(v - 1.0);
    };
    var f = function (v) {
        if (v === 0.0) {
            return false;
        };
        return g(v - 1.0);
    };
    var x = f(1.0);
    return !x;
})();
var main = function __do() {
    Effect_Console.logShow(Data_Show.showBoolean)(test)();
    return Effect_Console.log("Done")();
};
export {
    test,
    main
};
