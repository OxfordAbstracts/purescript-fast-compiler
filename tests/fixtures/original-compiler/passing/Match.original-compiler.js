import * as Effect_Console from "../Effect.Console/index.js";
var Foo = /* #__PURE__ */ (function () {
    function Foo() {

    };
    Foo.value = new Foo();
    return Foo;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foo = function (f) {
    return "foo";
};
export {
    Foo,
    foo,
    main
};
