import * as Effect_Console from "../Effect.Console/index.js";
var Foo = /* #__PURE__ */ (function () {
    function Foo() {

    };
    Foo.value = new Foo();
    return Foo;
})();
var classNameFoo = {
    foo: function (v) {
        return 0;
    }
};
var classNameFoo1 = {
    foo: function (v) {
        return 0;
    }
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foo = function (dict) {
    return dict.foo;
};
export {
    foo,
    Foo,
    main,
    classNameFoo1,
    classNameFoo
};
