import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var bug = function (a) {
    return function (b) {
        return 0.0 - (a - b);
    };
};
var main = function __do() {
    Test_Assert.assert(bug(0.0)(2.0) === 2.0)();
    Test_Assert.assert(0.0 - (0.0 - 2.0) === 2.0)();
    Test_Assert.assert(0.0 - (0.0 + 2.0) === -2.0)();
    Test_Assert.assert(6.0 / (3.0 * 2.0) === 1.0)();
    Test_Assert.assert((6.0 / 3.0) * 2.0 === 4.0)();
    Test_Assert.assert(!(1.0 < 0.0) === true)();
    Test_Assert.assert(!(-1.0 < 0.0) === false)();
    Test_Assert.assert(-(1.0 + 10.0) === -11.0)();
    Test_Assert.assert((2.0 * 3.0) / 4.0 === 1.5)();
    Test_Assert.assert((1.0 * 2.0 * 3.0 * 4.0 * 5.0) / 6.0 === 20.0)();
    Test_Assert.assert((1.0 + 10.0) - 5.0 === 6.0)();
    Test_Assert.assert(1.0 + 10.0 * 5.0 === 51.0)();
    Test_Assert.assert(10.0 * 5.0 - 1.0 === 49.0)();
    return Effect_Console.log("Done")();
};
export {
    bug,
    main
};
