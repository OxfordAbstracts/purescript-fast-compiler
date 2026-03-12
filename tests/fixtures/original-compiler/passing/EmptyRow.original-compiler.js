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
var test = /* #__PURE__ */ (function () {
    return new Foo({});
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Foo,
    test,
    main
};
