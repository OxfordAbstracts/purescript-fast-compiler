import * as Effect_Console from "../Effect.Console/index.js";
var Foo = /* #__PURE__ */ (function () {
    function Foo(value0) {
        this.value0 = value0;
    };
    Foo.create = function (value0) {
        return new Foo(value0);
    };
    return Foo;
})();
var Bar = /* #__PURE__ */ (function () {
    function Bar() {

    };
    Bar.value = new Bar();
    return Bar;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foo = function (dictPartial) {
    return function (v) {
        if (v instanceof Foo && v.value0.length === 0) {
            return Bar.value;
        };
        throw new Error("Failed pattern match at Main (line 10, column 1 - line 10, column 19): " + [ v.constructor.name ]);
    };
};
export {
    Foo,
    Bar,
    foo,
    main
};
