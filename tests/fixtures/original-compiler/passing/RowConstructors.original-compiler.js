import * as Control_Category from "../Control.Category/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var wildcard$prime = function (v) {
    return v.q;
};
var wildcard = function (v) {
    return {
        x: v.w,
        y: v.w,
        z: v.w,
        w: v.w
    };
};
var quux$prime = {
    x: 0.0,
    y: 0.0,
    z: 0.0,
    q: 0.0,
    "q'": 0.0
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var id$prime = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var foo = {
    x: 0.0,
    y: 0.0,
    z: 0.0
};
var foo$prime = foo;
var quux = {
    f: foo$prime,
    x: 0.0,
    y: 0.0,
    z: 0.0,
    q: 0.0
};
var baz = {
    x: 0.0,
    y: 0.0,
    z: 0.0,
    w: 0.0
};
var bar = {
    x: 0.0,
    y: 0.0,
    z: 0.0
};
var bar$prime = bar;
export {
    foo,
    bar,
    id$prime,
    foo$prime,
    bar$prime,
    baz,
    quux,
    quux$prime,
    wildcard,
    wildcard$prime,
    main
};
