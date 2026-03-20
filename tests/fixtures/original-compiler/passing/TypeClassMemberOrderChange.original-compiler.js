import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var val = function (dict) {
    return dict.val;
};
var testBoolean = {
    val: true,
    fn: function (x) {
        return function (y) {
            return y;
        };
    }
};
var fn = function (dict) {
    return dict.fn;
};
var main = function __do() {
    Effect_Console.log(Data_Show.show(Data_Show.showBoolean)(fn(testBoolean)(true)(val(testBoolean))))();
    return Effect_Console.log("Done")();
};
export {
    fn,
    val,
    main,
    testBoolean
};
