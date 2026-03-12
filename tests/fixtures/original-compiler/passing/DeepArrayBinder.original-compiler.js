import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
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
var match2 = function (v) {
    if (v instanceof Cons && v.value1 instanceof Cons) {
        return v.value0 * v.value1.value0 + match2(v.value1.value1);
    };
    return 0.0;
};
var main = /* #__PURE__ */ (function () {
    var result = match2(new Cons(1.0, new Cons(2.0, new Cons(3.0, new Cons(4.0, new Cons(5.0, new Cons(6.0, new Cons(7.0, new Cons(8.0, new Cons(9.0, Nil.value))))))))));
    return function __do() {
        Test_Assert["assert$prime"]("Incorrect result!")(result === 100.0)();
        return Effect_Console.log("Done")();
    };
})();
export {
    Cons,
    Nil,
    match2,
    main
};
