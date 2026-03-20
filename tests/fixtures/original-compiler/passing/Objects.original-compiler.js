import * as Effect_Console from "../Effect.Console/index.js";
var typed = {
    foo: 0.0
};
var test7 = function (v) {
    return v.b;
};
var test6 = /* #__PURE__ */ (function () {
    var $5 = {
        "***": 1.0
    };
    return $5["***"];
})();
var test5 = /* #__PURE__ */ (function () {
    var $7 = {
        "***": 1.0
    };
    return $7["***"];
})();
var test3 = /* #__PURE__ */ (function () {
    return typed.foo;
})();
var test2 = function (x) {
    return x["!@#"];
};
var test4 = /* #__PURE__ */ (function () {
    var weirdObj = {
        "!@#": 1.0
    };
    return test2(weirdObj);
})();
var test = function (x) {
    return x.foo + x.bar + 1.0;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var g = /* #__PURE__ */ (function (a) {
    return a.f({
        x: 1.0,
        y: "y"
    });
})({
    f: function (o) {
        return o.x + 1.0;
    }
});
var f = /* #__PURE__ */ (function (a) {
    return a.b.c;
})({
    b: {
        c: 1.0,
        d: "Hello"
    },
    e: "World"
});
var append = function (o) {
    return {
        foo: o.foo,
        bar: 1.0
    };
};
var apTest = /* #__PURE__ */ append({
    foo: "Foo",
    baz: "Baz"
});
export {
    test,
    append,
    apTest,
    f,
    g,
    typed,
    test2,
    test3,
    test4,
    test5,
    test6,
    test7,
    main
};
