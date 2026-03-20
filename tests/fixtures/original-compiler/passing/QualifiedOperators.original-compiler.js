import * as Effect_Console from "../Effect.Console/index.js";
import * as Foo from "../Foo/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var main = function __do() {
    Test_Assert.assert(Foo.tie(4)(10) === 33)();
    Test_Assert.assert(Foo.tie(4)(10) === 33)();
    return Effect_Console.log("Done")();
};
export {
    main
};
