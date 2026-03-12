import * as Effect_Console from "../Effect.Console/index.js";
var Cons = /* #__PURE__ */ (function () {
    function Cons(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Cons.create = function (value0) {
        return function (value1) {
            return new Cons(value0, value1);
        };
    };
    return Cons;
})();
var Nil = /* #__PURE__ */ (function () {
    function Nil() {

    };
    Nil.value = new Nil();
    return Nil;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var f = function (v) {
    if (v instanceof Cons) {
        return v.value0.x + v.value0.y | 0;
    };
    return 0;
};
export {
    Cons,
    Nil,
    f,
    main
};
