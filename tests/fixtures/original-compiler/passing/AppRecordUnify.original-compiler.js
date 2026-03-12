import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var apply = function (x) {
    return x;
};
var test = /* #__PURE__ */ apply({
    x: 42
});
export {
    apply,
    test,
    main
};
