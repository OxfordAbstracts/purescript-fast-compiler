import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var Baz$prime$prime = /* #__PURE__ */ (function () {
    function Baz$prime$prime() {

    };
    Baz$prime$prime.value = new Baz$prime$prime();
    return Baz$prime$prime;
})();
var Baz$prime = /* #__PURE__ */ (function () {
    function Baz$prime() {

    };
    Baz$prime.value = new Baz$prime();
    return Baz$prime;
})();
var Bar$prime = function (x) {
    return x;
};
var Foo$prime = /* #__PURE__ */ (function () {
    function Foo$prime(value0) {
        this.value0 = value0;
    };
    Foo$prime.create = function (value0) {
        return new Foo$prime(value0);
    };
    return Foo$prime;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var h = function (v) {
    if (v <= 10) {
        return v * 2 | 0;
    };
    if (Data_Boolean.otherwise) {
        return 10;
    };
    throw new Error("Failed pattern match at Main (line 25, column 1 - line 25, column 15): " + [ v.constructor.name ]);
};
var h$prime = /* #__PURE__ */ h(4);
var g = function (v) {
    if (v instanceof Baz$prime$prime) {
        return 0;
    };
    if (v instanceof Baz$prime) {
        return 1;
    };
    throw new Error("Failed pattern match at Main (line 18, column 1 - line 18, column 16): " + [ v.constructor.name ]);
};
var g$prime = /* #__PURE__ */ (function () {
    return g(Baz$prime$prime.value);
})();
var f = function (a) {
    return true;
};
var f$prime = /* #__PURE__ */ (function () {
    return f(new Foo$prime(0));
})();
export {
    Bar$prime,
    Foo$prime,
    Baz$prime$prime,
    Baz$prime,
    f,
    f$prime,
    g,
    g$prime,
    h,
    h$prime,
    main
};
