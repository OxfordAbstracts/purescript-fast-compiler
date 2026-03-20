import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var g = function (v) {
    if (v === "a") {
        return "a";
    };
    return "b";
};
var f = function (v) {
    if (v === 1) {
        return 1;
    };
    return 0;
};
var main = function __do() {
    Test_Assert.assert(f(1) === 1)();
    Test_Assert.assert(f(0) === 0)();
    Test_Assert.assert(g("a") === "a")();
    Test_Assert.assert(g("b") === "b")();
    return Effect_Console.log("Done")();
};
export {
    f,
    g,
    main
};
