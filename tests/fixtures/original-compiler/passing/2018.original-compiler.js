import * as A from "../A/index.js";
import * as B from "../B/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ (function () {
    var tmp = A.foo(B.X.value);
    return Effect_Console.log("Done");
})();
export {
    main
};
