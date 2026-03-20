import * as Effect_Console from "../Effect.Console/index.js";
var test = /* #__PURE__ */ (function (x) {
    return x * 2.0;
})(/* #__PURE__ */ (function (x) {
    return x + 1.0;
})(4.0));
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    test,
    main
};
