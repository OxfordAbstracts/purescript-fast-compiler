import * as Effect_Console from "../Effect.Console/index.js";
var Foo = /* #__PURE__ */ (function () {
    function Foo() {

    };
    Foo.value = new Foo();
    return Foo;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var eqFoo = {
    eq: function (v) {
        return function (v1) {
            return true;
        };
    }
};
export {
    Foo,
    main,
    eqFoo
};
