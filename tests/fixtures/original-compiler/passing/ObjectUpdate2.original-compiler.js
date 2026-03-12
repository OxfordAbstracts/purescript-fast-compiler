import * as Effect_Console from "../Effect.Console/index.js";
var x = {
    baz: "baz"
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var blah = function (x1) {
    return x1;
};
var test = /* #__PURE__ */ blah({
    baz: "blah"
});
export {
    x,
    blah,
    test,
    main
};
