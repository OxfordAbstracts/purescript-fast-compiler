import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var getFoo = function (o) {
    return o.foo;
};
var foo = function (s) {
    return s;
};
var f = function (g) {
    var v = g({
        x: "Hello"
    });
    return v.x;
};
export {
    foo,
    getFoo,
    f,
    main
};
