import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var b = function (dict) {
    return dict.b;
};
var a = function (dict) {
    return dict.a;
};
var bNumber = {
    b: function (v) {
        if (v === 0.0) {
            return false;
        };
        return a(aNumber)(v - 1.0);
    }
};
var aNumber = {
    a: function (v) {
        if (v === 0.0) {
            return true;
        };
        return b(bNumber)(v - 1.0);
    }
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showBoolean)(a(aNumber)(10.0))();
    return Effect_Console.log("Done")();
};
export {
    a,
    b,
    main,
    aNumber,
    bNumber
};
