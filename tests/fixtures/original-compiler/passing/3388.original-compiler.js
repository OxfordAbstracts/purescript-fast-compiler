import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ (function () {
    var x = {
        a: 42,
        b: "foo"
    };
    var v = {
        b: x.b,
        a: 43
    };
    return Effect_Console.log("Done");
})();
export {
    main
};
