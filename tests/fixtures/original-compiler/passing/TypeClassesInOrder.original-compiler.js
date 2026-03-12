import * as Effect_Console from "../Effect.Console/index.js";
var fooString = {
    foo: function (s) {
        return s;
    }
};
var foo = function (dict) {
    return dict.foo;
};
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ foo(fooString)("Done"));
export {
    foo,
    main,
    fooString
};
