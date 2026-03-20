import * as Control_Category from "../Control.Category/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var foldl = /* #__PURE__ */ Data_Foldable.foldl(Data_Foldable.foldableArray);
var foldr = /* #__PURE__ */ Data_Foldable.foldr(Data_Foldable.foldableArray);
var foldMap = /* #__PURE__ */ Data_Foldable.foldMap(Data_Foldable.foldableArray);
var assertEqual$prime = /* #__PURE__ */ Test_Assert["assertEqual$prime"](Data_Eq.eqString)(Data_Show.showString);
var M0 = /* #__PURE__ */ (function () {
    function M0() {

    };
    M0.value = new M0();
    return M0;
})();
var M1 = /* #__PURE__ */ (function () {
    function M1(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    M1.create = function (value0) {
        return function (value1) {
            return new M1(value0, value1);
        };
    };
    return M1;
})();
var M2 = /* #__PURE__ */ (function () {
    function M2(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    M2.create = function (value0) {
        return function (value1) {
            return new M2(value0, value1);
        };
    };
    return M2;
})();
var M3 = /* #__PURE__ */ (function () {
    function M3(value0) {
        this.value0 = value0;
    };
    M3.create = function (value0) {
        return new M3(value0);
    };
    return M3;
})();
var M4 = /* #__PURE__ */ (function () {
    function M4(value0) {
        this.value0 = value0;
    };
    M4.create = function (value0) {
        return new M4(value0);
    };
    return M4;
})();
var M5 = /* #__PURE__ */ (function () {
    function M5(value0) {
        this.value0 = value0;
    };
    M5.create = function (value0) {
        return new M5(value0);
    };
    return M5;
})();
var M6 = /* #__PURE__ */ (function () {
    function M6(value0, value1, value2, value3, value4, value5, value6, value7) {
        this.value0 = value0;
        this.value1 = value1;
        this.value2 = value2;
        this.value3 = value3;
        this.value4 = value4;
        this.value5 = value5;
        this.value6 = value6;
        this.value7 = value7;
    };
    M6.create = function (value0) {
        return function (value1) {
            return function (value2) {
                return function (value3) {
                    return function (value4) {
                        return function (value5) {
                            return function (value6) {
                                return function (value7) {
                                    return new M6(value0, value1, value2, value3, value4, value5, value6, value7);
                                };
                            };
                        };
                    };
                };
            };
        };
    };
    return M6;
})();
var M7 = /* #__PURE__ */ (function () {
    function M7(value0) {
        this.value0 = value0;
    };
    M7.create = function (value0) {
        return new M7(value0);
    };
    return M7;
})();
var recordValue = {
    a: "a",
    zArrayA: [ "c" ],
    fa: [ "b" ],
    ignore: 1,
    arrayIgnore: [ 2, 3 ],
    fIgnore: [ 4 ]
};
var m7 = /* #__PURE__ */ (function () {
    return new M7([ [ {
        nested: recordValue
    } ] ]);
})();
var m6 = /* #__PURE__ */ (function () {
    return new M6(1, "a", [  ], [ "b" ], [ "c" ], [  ], recordValue, {
        nested: recordValue
    });
})();
var m5 = /* #__PURE__ */ (function () {
    return new M5({
        nested: recordValue
    });
})();
var m4 = /* #__PURE__ */ (function () {
    return new M4(recordValue);
})();
var m3 = /* #__PURE__ */ (function () {
    return new M3([ "a", "b", "c" ]);
})();
var m2 = /* #__PURE__ */ (function () {
    return new M2(0, identity);
})();
var m1 = /* #__PURE__ */ (function () {
    return new M1("a", [ "b", "c" ]);
})();
var m0 = /* #__PURE__ */ (function () {
    return M0.value;
})();
var foldrStr = function (dictFoldable) {
    return Data_Foldable.foldr(dictFoldable)(function (next) {
        return function (acc) {
            return next + (">" + acc);
        };
    })("Start");
};
var foldlStr = function (dictFoldable) {
    return Data_Foldable.foldl(dictFoldable)(function (acc) {
        return function (next) {
            return acc + ("<" + next);
        };
    })("Start");
};
var foldableM = function (dictFoldable) {
    var foldl1 = Data_Foldable.foldl(dictFoldable);
    var foldr1 = Data_Foldable.foldr(dictFoldable);
    var foldMap1 = Data_Foldable.foldMap(dictFoldable);
    return {
        foldl: function (f) {
            return function (z) {
                return function (m) {
                    if (m instanceof M0) {
                        return z;
                    };
                    if (m instanceof M1) {
                        return foldl(f)(f(z)(m.value0))(m.value1);
                    };
                    if (m instanceof M2) {
                        return z;
                    };
                    if (m instanceof M3) {
                        return foldl1(f)(z)(m.value0);
                    };
                    if (m instanceof M4) {
                        return foldl(f)(foldl1(f)(f(z)(m.value0.a))(m.value0.fa))(m.value0.zArrayA);
                    };
                    if (m instanceof M5) {
                        return foldl(f)(foldl1(f)(f(z)(m.value0.nested.a))(m.value0.nested.fa))(m.value0.nested.zArrayA);
                    };
                    if (m instanceof M6) {
                        return foldl(f)(foldl1(f)(f(foldl(f)(foldl1(f)(f(foldl1(f)(foldl(f)(f(z)(m.value1))(m.value3))(m.value4))(m.value6.a))(m.value6.fa))(m.value6.zArrayA))(m.value7.nested.a))(m.value7.nested.fa))(m.value7.nested.zArrayA);
                    };
                    if (m instanceof M7) {
                        return foldl1(foldl1(function (v1) {
                            return function (v2) {
                                return foldl(f)(foldl1(f)(f(v1)(v2.nested.a))(v2.nested.fa))(v2.nested.zArrayA);
                            };
                        }))(z)(m.value0);
                    };
                    throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
                };
            };
        },
        foldr: function (f) {
            return function (z) {
                return function (m) {
                    if (m instanceof M0) {
                        return z;
                    };
                    if (m instanceof M1) {
                        return f(m.value0)(foldr(f)(z)(m.value1));
                    };
                    if (m instanceof M2) {
                        return z;
                    };
                    if (m instanceof M3) {
                        return foldr1(f)(z)(m.value0);
                    };
                    if (m instanceof M4) {
                        return f(m.value0.a)(foldr1(f)(foldr(f)(z)(m.value0.zArrayA))(m.value0.fa));
                    };
                    if (m instanceof M5) {
                        return f(m.value0.nested.a)(foldr1(f)(foldr(f)(z)(m.value0.nested.zArrayA))(m.value0.nested.fa));
                    };
                    if (m instanceof M6) {
                        return f(m.value1)(foldr(f)(foldr1(f)(f(m.value6.a)(foldr1(f)(foldr(f)(f(m.value7.nested.a)(foldr1(f)(foldr(f)(z)(m.value7.nested.zArrayA))(m.value7.nested.fa)))(m.value6.zArrayA))(m.value6.fa)))(m.value4))(m.value3));
                    };
                    if (m instanceof M7) {
                        return foldr1(Data_Function.flip(foldr1(function (v1) {
                            return function (v2) {
                                return f(v1.nested.a)(foldr1(f)(foldr(f)(v2)(v1.nested.zArrayA))(v1.nested.fa));
                            };
                        })))(z)(m.value0);
                    };
                    throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
                };
            };
        },
        foldMap: function (dictMonoid) {
            var mempty = Data_Monoid.mempty(dictMonoid);
            var append1 = Data_Semigroup.append(dictMonoid.Semigroup0());
            var foldMap2 = foldMap(dictMonoid);
            var foldMap3 = foldMap1(dictMonoid);
            return function (f) {
                return function (m) {
                    if (m instanceof M0) {
                        return mempty;
                    };
                    if (m instanceof M1) {
                        return append1(f(m.value0))(foldMap2(f)(m.value1));
                    };
                    if (m instanceof M2) {
                        return mempty;
                    };
                    if (m instanceof M3) {
                        return foldMap3(f)(m.value0);
                    };
                    if (m instanceof M4) {
                        return append1(f(m.value0.a))(append1(foldMap3(f)(m.value0.fa))(foldMap2(f)(m.value0.zArrayA)));
                    };
                    if (m instanceof M5) {
                        return append1(f(m.value0.nested.a))(append1(foldMap3(f)(m.value0.nested.fa))(foldMap2(f)(m.value0.nested.zArrayA)));
                    };
                    if (m instanceof M6) {
                        return append1(f(m.value1))(append1(foldMap2(f)(m.value3))(append1(foldMap3(f)(m.value4))(append1(f(m.value6.a))(append1(foldMap3(f)(m.value6.fa))(append1(foldMap2(f)(m.value6.zArrayA))(append1(f(m.value7.nested.a))(append1(foldMap3(f)(m.value7.nested.fa))(foldMap2(f)(m.value7.nested.zArrayA)))))))));
                    };
                    if (m instanceof M7) {
                        return foldMap3(foldMap3(function (v1) {
                            return append1(f(v1.nested.a))(append1(foldMap3(f)(v1.nested.fa))(foldMap2(f)(v1.nested.zArrayA)));
                        }))(m.value0);
                    };
                    throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
                };
            };
        }
    };
};
var foldableM1 = /* #__PURE__ */ foldableM(Data_Foldable.foldableArray);
var foldlStr1 = /* #__PURE__ */ foldlStr(foldableM1);
var foldrStr1 = /* #__PURE__ */ foldrStr(foldableM1);
var foldMapStr = function (dictFoldable) {
    return Data_Foldable.foldMap(dictFoldable)(Data_Monoid.monoidString)(identity);
};
var foldMapStr1 = /* #__PURE__ */ foldMapStr(foldableM1);
var main = function __do() {
    assertEqual$prime("foldl - M0")({
        expected: "Start",
        actual: foldlStr1(m0)
    })();
    assertEqual$prime("foldl - M1")({
        expected: "Start<a<b<c",
        actual: foldlStr1(m1)
    })();
    assertEqual$prime("foldl - M2")({
        expected: "Start",
        actual: foldlStr1(m2)
    })();
    assertEqual$prime("foldl - M3")({
        expected: "Start<a<b<c",
        actual: foldlStr1(m3)
    })();
    assertEqual$prime("foldl - M4")({
        expected: "Start<a<b<c",
        actual: foldlStr1(m4)
    })();
    assertEqual$prime("foldl - M5")({
        expected: "Start<a<b<c",
        actual: foldlStr1(m5)
    })();
    assertEqual$prime("foldl - M6")({
        expected: "Start<a<b<c<a<b<c<a<b<c",
        actual: foldlStr1(m6)
    })();
    assertEqual$prime("foldl - M7")({
        expected: "Start<a<b<c",
        actual: foldlStr1(m7)
    })();
    assertEqual$prime("foldr - M0")({
        expected: "Start",
        actual: foldrStr1(m0)
    })();
    assertEqual$prime("foldr - M1")({
        expected: "a>b>c>Start",
        actual: foldrStr1(m1)
    })();
    assertEqual$prime("foldr - M2")({
        expected: "Start",
        actual: foldrStr1(m2)
    })();
    assertEqual$prime("foldr - M3")({
        expected: "a>b>c>Start",
        actual: foldrStr1(m3)
    })();
    assertEqual$prime("foldr - M4")({
        expected: "a>b>c>Start",
        actual: foldrStr1(m4)
    })();
    assertEqual$prime("foldr - M5")({
        expected: "a>b>c>Start",
        actual: foldrStr1(m5)
    })();
    assertEqual$prime("foldr - M6")({
        expected: "a>b>c>a>b>c>a>b>c>Start",
        actual: foldrStr1(m6)
    })();
    assertEqual$prime("foldr - M7")({
        expected: "a>b>c>Start",
        actual: foldrStr1(m7)
    })();
    assertEqual$prime("foldMap - M0")({
        expected: "",
        actual: foldMapStr1(m0)
    })();
    assertEqual$prime("foldMap - M1")({
        expected: "abc",
        actual: foldMapStr1(m1)
    })();
    assertEqual$prime("foldMap - M2")({
        expected: "",
        actual: foldMapStr1(m2)
    })();
    assertEqual$prime("foldMap - M3")({
        expected: "abc",
        actual: foldMapStr1(m3)
    })();
    assertEqual$prime("foldMap - M4")({
        expected: "abc",
        actual: foldMapStr1(m4)
    })();
    assertEqual$prime("foldMap - M5")({
        expected: "abc",
        actual: foldMapStr1(m5)
    })();
    assertEqual$prime("foldMap - M6")({
        expected: "abcabcabc",
        actual: foldMapStr1(m6)
    })();
    assertEqual$prime("foldMap - M7")({
        expected: "abc",
        actual: foldMapStr1(m7)
    })();
    return Effect_Console.log("Done")();
};
export {
    M0,
    M1,
    M2,
    M3,
    M4,
    M5,
    M6,
    M7,
    foldlStr,
    foldrStr,
    foldMapStr,
    m0,
    m1,
    m2,
    m3,
    m4,
    m5,
    m6,
    m7,
    recordValue,
    main,
    foldableM
};
