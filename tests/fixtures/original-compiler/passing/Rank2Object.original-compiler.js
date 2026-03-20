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
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foo = function (v) {
    return v.value0.id(0.0);
};
export {
    Foo,
    foo,
    main
};
