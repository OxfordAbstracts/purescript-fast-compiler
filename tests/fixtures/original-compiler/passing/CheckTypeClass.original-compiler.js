import * as Effect_Console from "../Effect.Console/index.js";
var Bar = /* #__PURE__ */ (function () {
    function Bar() {

    };
    Bar.value = new Bar();
    return Bar;
})();
var mkBar = function (v) {
    return Bar.value;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foo = function (dict) {
    return dict.foo;
};
var foo_ = function (dictFoo) {
    var foo1 = foo(dictFoo);
    return function (x) {
        return foo1((function (dictFoo1) {
            return mkBar;
        })(dictFoo)(x));
    };
};
export {
    foo,
    Bar,
    foo_,
    mkBar,
    main
};
