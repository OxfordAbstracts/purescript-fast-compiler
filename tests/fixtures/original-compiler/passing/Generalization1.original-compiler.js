import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var logShow = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showInt);
var sum = function (dictSemiring) {
    var add = Data_Semiring.add(dictSemiring);
    return function (x) {
        return function (y) {
            return add(x)(y);
        };
    };
};
var sum1 = /* #__PURE__ */ sum(Data_Semiring.semiringInt);
var main = function __do() {
    Effect_Console.logShow(Data_Show.showNumber)(sum(Data_Semiring.semiringNumber)(1.0)(2.0))();
    logShow(sum1(1)(2))();
    return Effect_Console.log("Done")();
};
export {
    main,
    sum
};
