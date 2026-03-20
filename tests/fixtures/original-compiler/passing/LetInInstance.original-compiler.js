import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fooString = {
    foo: /* #__PURE__ */ (function () {
        var go = function (s) {
            return s;
        };
        return go;
    })()
};
var foo = function (dict) {
    return dict.foo;
};
export {
    foo,
    main,
    fooString
};
