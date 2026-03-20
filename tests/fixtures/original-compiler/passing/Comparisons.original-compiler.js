import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var main = function __do() {
    Test_Assert.assert(1.0 < 2.0)();
    Test_Assert.assert(2.0 === 2.0)();
    Test_Assert.assert(3.0 > 1.0)();
    Test_Assert.assert("a" < "b")();
    Test_Assert.assert("a" === "a")();
    Test_Assert.assert("z" > "a")();
    return Effect_Console.log("Done")();
};
export {
    main
};
