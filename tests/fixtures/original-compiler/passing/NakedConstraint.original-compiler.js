import * as Effect_Console from "../Effect.Console/index.js";
var Nil = /* #__PURE__ */ (function () {
    function Nil() {

    };
    Nil.value = new Nil();
    return Nil;
})();
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
var main = /* #__PURE__ */ Effect_Console.log("Done");
var head = function () {
    return function (v) {
        if (v instanceof Cons) {
            return v.value0;
        };
        throw new Error("Failed pattern match at Main (line 7, column 1 - line 7, column 35): " + [ v.constructor.name ]);
    };
};
export {
    Nil,
    Cons,
    head,
    main
};
