import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var main = function __do() {
    Test_Assert.assert(0.0 === 0.0)();
    var x1 = 1.0 + 1.0;
    return Effect_Console.log("Done")();
};
export {
    main
};
