import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var foo = function (foo1) {
    var foo_1 = function (v) {
        return foo1;
    };
    var foo_2 = foo_1(Data_Unit.unit) + 1.0;
    return foo_2;
};
var main = function __do() {
    Test_Assert.assert(foo(1.0) === 2.0)();
    return Effect_Console.log("Done")();
};
export {
    foo,
    main
};
