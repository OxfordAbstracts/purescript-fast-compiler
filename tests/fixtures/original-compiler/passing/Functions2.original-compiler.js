import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var test = function ($$const) {
    return function (v) {
        return $$const;
    };
};
var main = /* #__PURE__ */ (function () {
    var value = test("Done")({});
    return function __do() {
        Test_Assert["assert$prime"]("Not done")(value === "Done")();
        return Effect_Console.log("Done")();
    };
})();
export {
    test,
    main
};
