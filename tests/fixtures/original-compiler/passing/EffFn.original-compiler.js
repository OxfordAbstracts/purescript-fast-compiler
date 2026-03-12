import * as $foreign from "./foreign.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var testRunFn = function __do() {
    var str = $foreign.add3("a", "b", "c");
    return Test_Assert.assert(str === "abc")();
};
var testBothWays = function __do() {
    return Test_Assert.assert(42 === 42)();
};
var main = function __do() {
    testBothWays();
    testRunFn();
    return Effect_Console.log("Done")();
};
export {
    add3
} from "./foreign.js";
export {
    testBothWays,
    testRunFn,
    main
};
