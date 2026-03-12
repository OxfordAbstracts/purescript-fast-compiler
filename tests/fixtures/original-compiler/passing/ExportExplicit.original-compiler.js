import * as Effect_Console from "../Effect.Console/index.js";
import * as M1 from "../M1/index.js";
var testZ = /* #__PURE__ */ (function () {
    return M1.Z.value;
})();
var testX = /* #__PURE__ */ (function () {
    return M1.X.value;
})();
var testFoo = M1.foo;
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    testX,
    testZ,
    testFoo,
    main
};
