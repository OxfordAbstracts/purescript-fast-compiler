import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var bindFlipped = /* #__PURE__ */ Control_Bind.bindFlipped(Effect.bindEffect);
var Y = /* #__PURE__ */ (function () {
    function Y(value0, value1, value2) {
        this.value0 = value0;
        this.value1 = value1;
        this.value2 = value2;
    };
    Y.create = function (value0) {
        return function (value1) {
            return function (value2) {
                return new Y(value0, value1, value2);
            };
        };
    };
    return Y;
})();
var X = function (x) {
    return x;
};
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
var patternWithParens = /* #__PURE__ */ (function () {
    var v1 = new Y(25252, "hello, world", false);
    var v2 = new Y(789, "world, hello", true);
    var $43 = [ 1, 2 ];
    if ($43.length === 2) {
        return 25252 === 25252 && (25252 === 25252 && (v1.value0 === 25252 && (v1.value1 === "hello, world" && (!v1.value2 && (v2.value1 === "world, hello" && ($43[0] === 1 && $43[1] === 2))))));
    };
    throw new Error("Failed pattern match at Main (line 119, column 5 - line 119, column 22): " + [ $43.constructor.name ]);
})();
var patternWithNamedBinder = /* #__PURE__ */ (function () {
    var $52 = {
        x: 10,
        y: 20
    };
    return $52.x === 10 && ($52.x === 10 && ($52.y === 20 && $52.y === 20));
})();
var patternSimple = /* #__PURE__ */ (function () {
    return 25252 === 25252;
})();
var patternNewtype = /* #__PURE__ */ (function () {
    return 123 === 123;
})();
var patternMultipleWithNormal = /* #__PURE__ */ (function () {
    var v1 = new Y(2525, "hello, world", false);
    return 25252 === 25252 && (2525 === 2525 && (25252 === 25252 && (v1.value0 === 2525 && (v1.value1 === "hello, world" && !v1.value2))));
})();
var patternMultiple = /* #__PURE__ */ (function () {
    var v1 = new Y(25252, "hello, world", false);
    var v2 = new Y(789, "world, hello", true);
    var $64 = [ 1, 2 ];
    if ($64.length === 2) {
        return 25252 === 25252 && (25252 === 25252 && (v1.value0 === 25252 && (v1.value1 === "hello, world" && (!v1.value2 && (v2.value1 === "world, hello" && ($64[0] === 1 && $64[1] === 2))))));
    };
    throw new Error("Failed pattern match at Main (line 75, column 5 - line 75, column 20): " + [ $64.constructor.name ]);
})();
var patternDoWithParens = /* #__PURE__ */ (function () {
    var v1 = new Y(25252, "hello, world", false);
    var v2 = new Y(789, "world, hello", true);
    var $77 = [ 1, 2 ];
    if ($77.length === 2) {
        return pure(25252 === 25252 && (25252 === 25252 && (v1.value0 === 25252 && (v1.value1 === "hello, world" && (!v1.value2 && (v2.value1 === "world, hello" && ($77[0] === 1 && $77[1] === 2)))))));
    };
    throw new Error("Failed pattern match at Main (line 131, column 5 - line 131, column 22): " + [ $77.constructor.name ]);
})();
var patternDoWithNamedBinder = /* #__PURE__ */ (function () {
    var $86 = {
        x: 10,
        y: 20
    };
    return pure($86.x === 10 && ($86.x === 10 && ($86.y === 20 && $86.y === 20)));
})();
var patternDoSimple = /* #__PURE__ */ (function () {
    return pure(25252 === 25252);
})();
var patternDoNewtype = /* #__PURE__ */ (function () {
    return pure(123 === 123);
})();
var patternDoMultipleWithNormal = /* #__PURE__ */ (function () {
    var v1 = new Y(2525, "hello, world", false);
    return pure(25252 === 25252 && (2525 === 2525 && (25252 === 25252 && (v1.value0 === 2525 && (v1.value1 === "hello, world" && !v1.value2)))));
})();
var patternDoMultiple = /* #__PURE__ */ (function () {
    var v1 = new Y(25252, "hello, world", false);
    var v2 = new Y(789, "world, hello", true);
    var $98 = [ 1, 2 ];
    if ($98.length === 2) {
        return pure(25252 === 25252 && (25252 === 25252 && (v1.value0 === 25252 && (v1.value1 === "hello, world" && (!v1.value2 && (v2.value1 === "world, hello" && ($98[0] === 1 && $98[1] === 2)))))));
    };
    throw new Error("Failed pattern match at Main (line 87, column 5 - line 87, column 20): " + [ $98.constructor.name ]);
})();
var patternDoDataIgnored = /* #__PURE__ */ (function () {
    var v = new Y(789, "world, hello", true);
    return pure(v.value1 === "world, hello");
})();
var patternDoData = /* #__PURE__ */ (function () {
    var v = new Y(456, "hello, world", false);
    return pure(v.value0 === 456 && (v.value1 === "hello, world" && !v.value2));
})();
var patternDoArray = /* #__PURE__ */ (function () {
    var $115 = [ 1, 2 ];
    if ($115.length === 2) {
        return pure($115[0] === 1 && $115[1] === 2);
    };
    throw new Error("Failed pattern match at Main (line 65, column 7 - line 65, column 22): " + [ $115.constructor.name ]);
})();
var patternDataIgnored = /* #__PURE__ */ (function () {
    var v = new Y(789, "world, hello", true);
    return v.value1 === "world, hello";
})();
var patternData = /* #__PURE__ */ (function () {
    var v = new Y(456, "hello, world", false);
    return v.value0 === 456 && (v.value1 === "hello, world" && !v.value2);
})();
var patternArray = /* #__PURE__ */ (function () {
    var $126 = [ 1, 2 ];
    if ($126.length === 2) {
        return $126[0] === 1 && $126[1] === 2;
    };
    throw new Error("Failed pattern match at Main (line 59, column 7 - line 59, column 22): " + [ $126.constructor.name ]);
})();
var eqList = function (dictEq) {
    var eq3 = Data_Eq.eq(dictEq);
    return {
        eq: function (xs) {
            return function (ys) {
                var go = function ($copy_v) {
                    return function ($copy_v1) {
                        return function ($copy_v2) {
                            var $tco_var_v = $copy_v;
                            var $tco_var_v1 = $copy_v1;
                            var $tco_done = false;
                            var $tco_result;
                            function $tco_loop(v, v1, v2) {
                                if (!v2) {
                                    $tco_done = true;
                                    return false;
                                };
                                if (v instanceof Nil && v1 instanceof Nil) {
                                    $tco_done = true;
                                    return v2;
                                };
                                if (v instanceof Cons && v1 instanceof Cons) {
                                    $tco_var_v = v.value1;
                                    $tco_var_v1 = v1.value1;
                                    $copy_v2 = v2 && eq3(v1.value0)(v.value0);
                                    return;
                                };
                                $tco_done = true;
                                return false;
                            };
                            while (!$tco_done) {
                                $tco_result = $tco_loop($tco_var_v, $tco_var_v1, $copy_v2);
                            };
                            return $tco_result;
                        };
                    };
                };
                return go(xs)(ys)(true);
            };
        }
    };
};
var eq2 = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ eqList(Data_Eq.eqInt));
var patternDoWithInfixOp = /* #__PURE__ */ (function () {
    var v = new Cons(1, new Cons(2, new Cons(3, new Cons(4, Nil.value))));
    if (v instanceof Cons) {
        return pure(v.value0 === 1 && eq2(v.value1)(new Cons(2, new Cons(3, new Cons(4, Nil.value)))));
    };
    throw new Error("Failed pattern match at Main (line 170, column 5 - line 170, column 33): " + [ v.constructor.name ]);
})();
var patternWithInfixOp = /* #__PURE__ */ (function () {
    var v = new Cons(1, new Cons(2, new Cons(3, new Cons(4, Nil.value))));
    if (v instanceof Cons) {
        return v.value0 === 1 && eq2(v.value1)(new Cons(2, new Cons(3, new Cons(4, Nil.value))));
    };
    throw new Error("Failed pattern match at Main (line 163, column 5 - line 163, column 33): " + [ v.constructor.name ]);
})();
var main = function __do() {
    Test_Assert["assert$prime"]("simple variable pattern")(patternSimple)();
    bindFlipped(Test_Assert["assert$prime"]("simple variable pattern with do"))(patternDoSimple)();
    Test_Assert["assert$prime"]("constructor pattern (newtype)")(patternNewtype)();
    bindFlipped(Test_Assert["assert$prime"]("constructor pattern (newtype) with do"))(patternDoNewtype)();
    Test_Assert["assert$prime"]("constructor pattern (data)")(patternData)();
    Test_Assert["assert$prime"]("constructor pattern with ignorances")(patternDataIgnored)();
    bindFlipped(Test_Assert["assert$prime"]("constructor pattern (data) with do"))(patternDoData)();
    bindFlipped(Test_Assert["assert$prime"]("constructor pattern with ignorances and do"))(patternDoDataIgnored)();
    Test_Assert["assert$prime"]("array pattern")(patternArray)();
    bindFlipped(Test_Assert["assert$prime"]("array pattern with do"))(patternDoArray)();
    Test_Assert["assert$prime"]("multiple patterns")(patternMultiple)();
    bindFlipped(Test_Assert["assert$prime"]("multiple patterns with do"))(patternDoMultiple)();
    Test_Assert["assert$prime"]("multiple patterns with normal let's")(patternMultipleWithNormal)();
    bindFlipped(Test_Assert["assert$prime"]("multiple patterns with normal let's and do"))(patternDoMultipleWithNormal)();
    Test_Assert["assert$prime"]("multiple patterns with parens")(patternWithParens)();
    bindFlipped(Test_Assert["assert$prime"]("multiple patterns with parens and do"))(patternDoWithParens)();
    Test_Assert["assert$prime"]("multiple patterns with named binder")(patternWithNamedBinder)();
    bindFlipped(Test_Assert["assert$prime"]("multiple patterns with named binder and do"))(patternDoWithNamedBinder)();
    Test_Assert["assert$prime"]("pattern with infix operator")(patternWithInfixOp)();
    bindFlipped(Test_Assert["assert$prime"]("pattern with infix operator and do"))(patternDoWithInfixOp)();
    return Effect_Console.log("Done")();
};
export {
    patternSimple,
    patternDoSimple,
    X,
    patternNewtype,
    patternDoNewtype,
    Y,
    patternData,
    patternDataIgnored,
    patternDoData,
    patternDoDataIgnored,
    patternArray,
    patternDoArray,
    patternMultiple,
    patternDoMultiple,
    patternMultipleWithNormal,
    patternDoMultipleWithNormal,
    patternWithParens,
    patternDoWithParens,
    patternWithNamedBinder,
    patternDoWithNamedBinder,
    Nil,
    Cons,
    patternWithInfixOp,
    patternDoWithInfixOp,
    main,
    eqList
};
