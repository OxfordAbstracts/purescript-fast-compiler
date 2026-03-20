import * as Effect_Console from "../Effect.Console/index.js";
var fooLogEff = {
    foo: Effect_Console.log
};
var foo = function (dict) {
    return dict.foo;
};
var main = /* #__PURE__ */ foo(fooLogEff)("Done");
export {
    foo,
    main,
    fooLogEff
};
