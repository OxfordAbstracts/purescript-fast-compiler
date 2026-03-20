import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foo = /* #__PURE__ */ (function () {
    var bar = function (r1) {
        return r1 + 1.0;
    };
    return bar;
})();
var r = /* #__PURE__ */ foo(2.0);
export {
    foo,
    r,
    main
};
