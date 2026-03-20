import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var g = function (y) {
    return y - 10.0;
};
var f = function (x) {
    return x * 10.0;
};
var main = function __do() {
    Effect_Console.log(Data_Show.show(Data_Show.showNumber)(f(g(100.0))))();
    return Effect_Console.log("Done")();
};
export {
    f,
    g,
    main
};
