import * as Effect_Console from "../Effect.Console/index.js";
import * as List from "../List/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var get3 = function (v) {
    return function (v1) {
        if (v1 instanceof List.Cons && v1.value1 instanceof List.Cons) {
            return v1.value1.value0;
        };
        return v;
    };
};
var get2 = function (v) {
    return function (v1) {
        if (v1 instanceof List.Cons && v1.value1 instanceof List.Cons) {
            return v1.value1.value0;
        };
        return v;
    };
};
var get1 = function (y) {
    return function (xs) {
        if (xs instanceof List.Cons && xs.value1 instanceof List.Cons) {
            return xs.value1.value0;
        };
        return y;
    };
};
var main = function __do() {
    Test_Assert["assert$prime"]("Incorrect result!")(get1(0)(new List.Cons(1, new List.Cons(2, new List.Cons(3, List.Nil.value)))) === 2)();
    Test_Assert["assert$prime"]("Incorrect result!")(get2(0)(new List.Cons(1, new List.Cons(2, new List.Cons(3, List.Nil.value)))) === 2)();
    Test_Assert["assert$prime"]("Incorrect result!")(get3(0.0)(new List.Cons(1.0, new List.Cons(2.0, new List.Cons(3.0, List.Nil.value)))) === 2.0)();
    return Effect_Console.log("Done")();
};
export {
    get1,
    get2,
    get3,
    main
};
