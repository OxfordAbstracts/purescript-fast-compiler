import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var mkValue = function (id) {
    return id;
};
var main = /* #__PURE__ */ (function () {
    var value = mkValue(1.0);
    return function __do() {
        Test_Assert.assert(value === 1.0)();
        return Effect_Console.log("Done")();
    };
})();
export {
    mkValue,
    main
};
