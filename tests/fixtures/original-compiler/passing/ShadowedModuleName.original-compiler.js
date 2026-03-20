import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_1 from "../Test/index.js";
var Test = /* #__PURE__ */ (function () {
    function Test() {

    };
    Test.value = new Test();
    return Test;
})();
var main = /* #__PURE__ */ (function () {
    return Effect_Console.log(Test_1.runZ(new Test_1.Z("Done")));
})();
export {
    Test,
    main
};
