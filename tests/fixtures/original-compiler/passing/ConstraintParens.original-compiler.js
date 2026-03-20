import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foo = function (dict) {
    return dict.foo;
};
var test = function (dictFoo) {
    return foo(dictFoo);
};
export {
    foo,
    test,
    main
};
