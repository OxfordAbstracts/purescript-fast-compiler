import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var foo = function () {
    return function (x) {
        return x;
    };
};
var main = /* #__PURE__ */ (function () {
    return Control_Applicative.when(Effect.applicativeEffect)(foo()(42) === 42)(Effect_Console.log("Done"));
})();
export {
    foo,
    main
};
