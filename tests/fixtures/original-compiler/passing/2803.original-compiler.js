import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var f = /* #__PURE__ */ Data_Semiring.add(Data_Semiring.semiringInt);
var g = function (a) {
    return function (b) {
        return a + b | 0;
    };
};
var main = /* #__PURE__ */ (function () {
    var $2 = g(10)(5) === 15;
    if ($2) {
        return Effect_Console.log("Done");
    };
    return Effect_Console.log("Failed");
})();
export {
    f,
    g,
    main
};
