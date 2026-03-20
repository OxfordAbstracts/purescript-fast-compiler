import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fooInt = undefined;
var foo = function (dict) {
    return dict.foo;
};
var bar = function (dict) {
    return dict.bar;
};
export {
    bar,
    foo,
    main,
    fooInt
};
