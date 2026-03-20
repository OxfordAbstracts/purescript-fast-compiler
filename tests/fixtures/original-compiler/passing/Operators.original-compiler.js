import * as Data_Function from "../Data.Function/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Other from "../Other/index.js";
var test3 = /* #__PURE__ */ (function () {
    return (function (x) {
        return function (y) {
            return x;
        };
    })(1.0 + 2.0 * (1.0 + 2.0))(true && (false || false));
})();
var test2 = /* #__PURE__ */ (function (x) {
    return x.foo(false);
})({
    foo: function (v) {
        return 1.0;
    }
});
var test19 = /* #__PURE__ */ (function () {
    return - - -1.0;
})();
var test18 = /* #__PURE__ */ (function () {
    return - -1.0;
})();
var test17 = /* #__PURE__ */ (function () {
    return - -1.0;
})();
var test14 = function (a) {
    return function (b) {
        return a < b;
    };
};
var test15 = function (a) {
    return function (b) {
        return Data_Function["const"](false)(test14(a)(b));
    };
};
var test10 = /* #__PURE__ */ Other.baz("Hello")("World");
var test1 = function (dictSemiring) {
    var add1 = Data_Semiring.add(dictSemiring);
    var mul1 = Data_Semiring.mul(dictSemiring);
    return function (x) {
        return function (y) {
            return function (z) {
                return add1(mul1(x)(y))(z(x)(y));
            };
        };
    };
};
var op5 = function (as) {
    return function (bs) {
        return as;
    };
};
var test11 = /* #__PURE__ */ op5([ 1.0, 2.0, 0.0 ])([ 4.0, 5.0, 6.0 ]);
var op4 = function (f) {
    return function (x) {
        return f(x);
    };
};
var test8 = /* #__PURE__ */ op4(Other.foo)("Hello World");
var test9 = /* #__PURE__ */ op4(Other.foo)("Hello World");
var op3 = function (s1) {
    return function (s2) {
        return s1 + s2;
    };
};
var test7 = /* #__PURE__ */ op3("Hello")("World!");
var op2 = function (x) {
    return function (y) {
        return x * y + y;
    };
};
var test5 = /* #__PURE__ */ op2(/* #__PURE__ */ op2(1.0)(2.0))(3.0);
var op1 = function (x) {
    return function (v) {
        return x;
    };
};
var k = function (x) {
    return function (y) {
        return x;
    };
};
var test4 = /* #__PURE__ */ k(1)(2);
var test6 = /* #__PURE__ */ k(function (x) {
    return x;
})(2.0)(3.0);
var main = /* #__PURE__ */ (function () {
    var t1 = test1(Data_Semiring.semiringNumber)(1.0)(2.0)(function (x) {
        return function (y) {
            return x + y;
        };
    });
    var t14 = test14(1.0)(2.0);
    var t15 = test15(1.0)(2.0);
    return Effect_Console.log("Done");
})();
export {
    op1,
    test1,
    test2,
    test3,
    k,
    test4,
    op2,
    test5,
    test6,
    op3,
    test7,
    op4,
    test8,
    test9,
    test10,
    op5,
    test11,
    test14,
    test15,
    test17,
    test18,
    test19,
    main
};
