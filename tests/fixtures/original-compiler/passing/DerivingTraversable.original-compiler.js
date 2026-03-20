import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Apply from "../Control.Apply/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Traversable from "../Data.Traversable/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var foldl = /* #__PURE__ */ Data_Foldable.foldl(Data_Foldable.foldableArray);
var foldr = /* #__PURE__ */ Data_Foldable.foldr(Data_Foldable.foldableArray);
var foldMap = /* #__PURE__ */ Data_Foldable.foldMap(Data_Foldable.foldableArray);
var traverse = /* #__PURE__ */ Data_Traversable.traverse(Data_Traversable.traversableArray);
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var eqArray = /* #__PURE__ */ Data_Eq.eqArray(Data_Eq.eqInt);
var eq1 = /* #__PURE__ */ Data_Eq.eq(eqArray);
var pure = /* #__PURE__ */ Control_Applicative.pure(Control_Applicative.applicativeArray);
var eqRec = /* #__PURE__ */ Data_Eq.eqRec();
var eqRowCons = /* #__PURE__ */ Data_Eq.eqRowCons(Data_Eq.eqRowNil)();
var eqArray1 = /* #__PURE__ */ Data_Eq.eqArray(Data_Eq.eqString);
var eqArray2 = /* #__PURE__ */ Data_Eq.eqArray(/* #__PURE__ */ eqRec(/* #__PURE__ */ eqRowCons({
    reflectSymbol: function () {
        return "nested";
    }
})(/* #__PURE__ */ eqRec(/* #__PURE__ */ Data_Eq.eqRowCons(/* #__PURE__ */ Data_Eq.eqRowCons(/* #__PURE__ */ Data_Eq.eqRowCons(/* #__PURE__ */ Data_Eq.eqRowCons(/* #__PURE__ */ Data_Eq.eqRowCons(/* #__PURE__ */ eqRowCons({
    reflectSymbol: function () {
        return "zArrayA";
    }
})(eqArray1))()({
    reflectSymbol: function () {
        return "ignore";
    }
})(Data_Eq.eqInt))()({
    reflectSymbol: function () {
        return "fa";
    }
})(eqArray1))()({
    reflectSymbol: function () {
        return "fIgnore";
    }
})(eqArray))()({
    reflectSymbol: function () {
        return "arrayIgnore";
    }
})(eqArray))()({
    reflectSymbol: function () {
        return "a";
    }
})(Data_Eq.eqString)))));
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
    function M2(value0) {
        this.value0 = value0;
    };
    M2.create = function (value0) {
        return new M2(value0);
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
var functorM = function (dictFunctor) {
    var map1 = Data_Functor.map(dictFunctor);
    return {
        map: function (f) {
            return function (m) {
                if (m instanceof M0) {
                    return M0.value;
                };
                if (m instanceof M1) {
                    return new M1(f(m.value0), map(f)(m.value1));
                };
                if (m instanceof M2) {
                    return new M2(m.value0);
                };
                if (m instanceof M3) {
                    return new M3(map1(f)(m.value0));
                };
                if (m instanceof M4) {
                    return new M4({
                        ignore: m.value0.ignore,
                        arrayIgnore: m.value0.arrayIgnore,
                        fIgnore: m.value0.fIgnore,
                        a: f(m.value0.a),
                        fa: map1(f)(m.value0.fa),
                        zArrayA: map(f)(m.value0.zArrayA)
                    });
                };
                if (m instanceof M5) {
                    return new M5({
                        nested: {
                            ignore: m.value0.nested.ignore,
                            arrayIgnore: m.value0.nested.arrayIgnore,
                            fIgnore: m.value0.nested.fIgnore,
                            a: f(m.value0.nested.a),
                            fa: map1(f)(m.value0.nested.fa),
                            zArrayA: map(f)(m.value0.nested.zArrayA)
                        }
                    });
                };
                if (m instanceof M6) {
                    return new M6(m.value0, f(m.value1), m.value2, map(f)(m.value3), map1(f)(m.value4), m.value5, {
                        ignore: m.value6.ignore,
                        arrayIgnore: m.value6.arrayIgnore,
                        fIgnore: m.value6.fIgnore,
                        a: f(m.value6.a),
                        fa: map1(f)(m.value6.fa),
                        zArrayA: map(f)(m.value6.zArrayA)
                    }, {
                        nested: {
                            ignore: m.value7.nested.ignore,
                            arrayIgnore: m.value7.nested.arrayIgnore,
                            fIgnore: m.value7.nested.fIgnore,
                            a: f(m.value7.nested.a),
                            fa: map1(f)(m.value7.nested.fa),
                            zArrayA: map(f)(m.value7.nested.zArrayA)
                        }
                    });
                };
                if (m instanceof M7) {
                    return new M7(map1(map1(function (v1) {
                        return {
                            nested: {
                                arrayIgnore: v1.nested.arrayIgnore,
                                fIgnore: v1.nested.fIgnore,
                                ignore: v1.nested.ignore,
                                a: f(v1.nested.a),
                                fa: map1(f)(v1.nested.fa),
                                zArrayA: map(f)(v1.nested.zArrayA)
                            }
                        };
                    }))(m.value0));
                };
                throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
            };
        }
    };
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
            var append = Data_Semigroup.append(dictMonoid.Semigroup0());
            var foldMap2 = foldMap(dictMonoid);
            var foldMap3 = foldMap1(dictMonoid);
            return function (f) {
                return function (m) {
                    if (m instanceof M0) {
                        return mempty;
                    };
                    if (m instanceof M1) {
                        return append(f(m.value0))(foldMap2(f)(m.value1));
                    };
                    if (m instanceof M2) {
                        return mempty;
                    };
                    if (m instanceof M3) {
                        return foldMap3(f)(m.value0);
                    };
                    if (m instanceof M4) {
                        return append(f(m.value0.a))(append(foldMap3(f)(m.value0.fa))(foldMap2(f)(m.value0.zArrayA)));
                    };
                    if (m instanceof M5) {
                        return append(f(m.value0.nested.a))(append(foldMap3(f)(m.value0.nested.fa))(foldMap2(f)(m.value0.nested.zArrayA)));
                    };
                    if (m instanceof M6) {
                        return append(f(m.value1))(append(foldMap2(f)(m.value3))(append(foldMap3(f)(m.value4))(append(f(m.value6.a))(append(foldMap3(f)(m.value6.fa))(append(foldMap2(f)(m.value6.zArrayA))(append(f(m.value7.nested.a))(append(foldMap3(f)(m.value7.nested.fa))(foldMap2(f)(m.value7.nested.zArrayA)))))))));
                    };
                    if (m instanceof M7) {
                        return foldMap3(foldMap3(function (v1) {
                            return append(f(v1.nested.a))(append(foldMap3(f)(v1.nested.fa))(foldMap2(f)(v1.nested.zArrayA)));
                        }))(m.value0);
                    };
                    throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
                };
            };
        }
    };
};
var traversableM = function (dictTraversable) {
    var traverse1 = Data_Traversable.traverse(dictTraversable);
    var functorM1 = functorM(dictTraversable.Functor0());
    var foldableM1 = foldableM(dictTraversable.Foldable1());
    return {
        traverse: function (dictApplicative) {
            var pure1 = Control_Applicative.pure(dictApplicative);
            var Apply0 = dictApplicative.Apply0();
            var apply = Control_Apply.apply(Apply0);
            var map1 = Data_Functor.map(Apply0.Functor0());
            var traverse2 = traverse(dictApplicative);
            var traverse3 = traverse1(dictApplicative);
            return function (f) {
                return function (m) {
                    if (m instanceof M0) {
                        return pure1(M0.value);
                    };
                    if (m instanceof M1) {
                        return apply(map1(function (v2) {
                            return function (v3) {
                                return new M1(v2, v3);
                            };
                        })(f(m.value0)))(traverse2(f)(m.value1));
                    };
                    if (m instanceof M2) {
                        return pure1(new M2(m.value0));
                    };
                    if (m instanceof M3) {
                        return map1(function (v1) {
                            return new M3(v1);
                        })(traverse3(f)(m.value0));
                    };
                    if (m instanceof M4) {
                        return apply(apply(map1(function (v1) {
                            return function (v2) {
                                return function (v3) {
                                    return new M4({
                                        ignore: m.value0.ignore,
                                        arrayIgnore: m.value0.arrayIgnore,
                                        fIgnore: m.value0.fIgnore,
                                        a: v1,
                                        fa: v2,
                                        zArrayA: v3
                                    });
                                };
                            };
                        })(f(m.value0.a)))(traverse3(f)(m.value0.fa)))(traverse2(f)(m.value0.zArrayA));
                    };
                    if (m instanceof M5) {
                        return apply(apply(map1(function (v1) {
                            return function (v2) {
                                return function (v3) {
                                    return new M5({
                                        nested: {
                                            ignore: m.value0.nested.ignore,
                                            arrayIgnore: m.value0.nested.arrayIgnore,
                                            fIgnore: m.value0.nested.fIgnore,
                                            a: v1,
                                            fa: v2,
                                            zArrayA: v3
                                        }
                                    });
                                };
                            };
                        })(f(m.value0.nested.a)))(traverse3(f)(m.value0.nested.fa)))(traverse2(f)(m.value0.nested.zArrayA));
                    };
                    if (m instanceof M6) {
                        return apply(apply(apply(apply(apply(apply(apply(apply(map1(function (v8) {
                            return function (v9) {
                                return function (v10) {
                                    return function (v11) {
                                        return function (v12) {
                                            return function (v13) {
                                                return function (v14) {
                                                    return function (v15) {
                                                        return function (v16) {
                                                            return new M6(m.value0, v8, m.value2, v9, v10, m.value5, {
                                                                ignore: m.value6.ignore,
                                                                arrayIgnore: m.value6.arrayIgnore,
                                                                fIgnore: m.value6.fIgnore,
                                                                a: v11,
                                                                fa: v12,
                                                                zArrayA: v13
                                                            }, {
                                                                nested: {
                                                                    ignore: m.value7.nested.ignore,
                                                                    arrayIgnore: m.value7.nested.arrayIgnore,
                                                                    fIgnore: m.value7.nested.fIgnore,
                                                                    a: v14,
                                                                    fa: v15,
                                                                    zArrayA: v16
                                                                }
                                                            });
                                                        };
                                                    };
                                                };
                                            };
                                        };
                                    };
                                };
                            };
                        })(f(m.value1)))(traverse2(f)(m.value3)))(traverse3(f)(m.value4)))(f(m.value6.a)))(traverse3(f)(m.value6.fa)))(traverse2(f)(m.value6.zArrayA)))(f(m.value7.nested.a)))(traverse3(f)(m.value7.nested.fa)))(traverse2(f)(m.value7.nested.zArrayA));
                    };
                    if (m instanceof M7) {
                        return map1(function (v1) {
                            return new M7(v1);
                        })(traverse3(traverse3(function (v1) {
                            return apply(apply(map1(function (v2) {
                                return function (v3) {
                                    return function (v4) {
                                        return {
                                            nested: {
                                                arrayIgnore: v1.nested.arrayIgnore,
                                                fIgnore: v1.nested.fIgnore,
                                                ignore: v1.nested.ignore,
                                                a: v2,
                                                fa: v3,
                                                zArrayA: v4
                                            }
                                        };
                                    };
                                };
                            })(f(v1.nested.a)))(traverse3(f)(v1.nested.fa)))(traverse2(f)(v1.nested.zArrayA));
                        }))(m.value0));
                    };
                    throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
                };
            };
        },
        sequence: function (dictApplicative) {
            return function (v) {
                return Data_Traversable.traverse(traversableM(dictTraversable))(dictApplicative)(identity)(v);
            };
        },
        Functor0: function () {
            return functorM1;
        },
        Foldable1: function () {
            return foldableM1;
        }
    };
};
var traversableM1 = /* #__PURE__ */ traversableM(Data_Traversable.traversableArray);
var eqM = function (dictEq1) {
    var eq11 = Data_Eq.eq1(dictEq1);
    var eq12 = eq11(Data_Eq.eqInt);
    return function (dictEq) {
        return function (dictEq2) {
            var eq13 = eq11(dictEq2);
            return function (dictEq3) {
                var eq3 = Data_Eq.eq(dictEq3);
                var eq4 = Data_Eq.eq(Data_Eq.eqArray(dictEq3));
                var eq14 = eq11(dictEq3);
                return {
                    eq: function (x) {
                        return function (y) {
                            if (x instanceof M0 && y instanceof M0) {
                                return true;
                            };
                            if (x instanceof M1 && y instanceof M1) {
                                return eq3(x.value0)(y.value0) && eq4(x.value1)(y.value1);
                            };
                            if (x instanceof M2 && y instanceof M2) {
                                return x.value0 === y.value0;
                            };
                            if (x instanceof M3 && y instanceof M3) {
                                return eq14(x.value0)(y.value0);
                            };
                            if (x instanceof M4 && y instanceof M4) {
                                return eq3(x.value0.a)(y.value0.a) && eq1(x.value0.arrayIgnore)(y.value0.arrayIgnore) && eq12(x.value0.fIgnore)(y.value0.fIgnore) && eq14(x.value0.fa)(y.value0.fa) && x.value0.ignore === y.value0.ignore && eq4(x.value0.zArrayA)(y.value0.zArrayA);
                            };
                            if (x instanceof M5 && y instanceof M5) {
                                return eq3(x.value0.nested.a)(y.value0.nested.a) && eq1(x.value0.nested.arrayIgnore)(y.value0.nested.arrayIgnore) && eq12(x.value0.nested.fIgnore)(y.value0.nested.fIgnore) && eq14(x.value0.nested.fa)(y.value0.nested.fa) && x.value0.nested.ignore === y.value0.nested.ignore && eq4(x.value0.nested.zArrayA)(y.value0.nested.zArrayA);
                            };
                            if (x instanceof M6 && y instanceof M6) {
                                return x.value0 === y.value0 && eq3(x.value1)(y.value1) && eq1(x.value2)(y.value2) && eq4(x.value3)(y.value3) && eq14(x.value4)(y.value4) && eq12(x.value5)(y.value5) && (eq3(x.value6.a)(y.value6.a) && eq1(x.value6.arrayIgnore)(y.value6.arrayIgnore) && eq12(x.value6.fIgnore)(y.value6.fIgnore) && eq14(x.value6.fa)(y.value6.fa) && x.value6.ignore === y.value6.ignore && eq4(x.value6.zArrayA)(y.value6.zArrayA)) && (eq3(x.value7.nested.a)(y.value7.nested.a) && eq1(x.value7.nested.arrayIgnore)(y.value7.nested.arrayIgnore) && eq12(x.value7.nested.fIgnore)(y.value7.nested.fIgnore) && eq14(x.value7.nested.fa)(y.value7.nested.fa) && x.value7.nested.ignore === y.value7.nested.ignore && eq4(x.value7.nested.zArrayA)(y.value7.nested.zArrayA));
                            };
                            if (x instanceof M7 && y instanceof M7) {
                                return eq13(x.value0)(y.value0);
                            };
                            return false;
                        };
                    }
                };
            };
        };
    };
};
var eq2 = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ Data_Eq.eqArray(/* #__PURE__ */ eqM(Data_Eq.eq1Array)(/* #__PURE__ */ Data_Eq.eqArray(eqArray2))(eqArray2)(Data_Eq.eqString)));
var traverseStr = function (dictTraversable) {
    return Data_Traversable.traverse(dictTraversable)(Control_Applicative.applicativeArray)(pure);
};
var traverseStr1 = /* #__PURE__ */ traverseStr(traversableM1);
var sequenceStr = function (dictTraversable) {
    return Data_Traversable.sequence(dictTraversable)(Control_Applicative.applicativeArray);
};
var sequenceStr1 = /* #__PURE__ */ sequenceStr(traversableM1);
var recordValue$prime = {
    a: [ "a" ],
    zArrayA: [ [ "c" ] ],
    fa: [ [ "b" ] ],
    ignore: 1,
    arrayIgnore: [ 2, 3 ],
    fIgnore: [ 4 ]
};
var recordValue = {
    a: "a",
    zArrayA: [ "c" ],
    fa: [ "b" ],
    ignore: 1,
    arrayIgnore: [ 2, 3 ],
    fIgnore: [ 4 ]
};
var m7$prime = /* #__PURE__ */ (function () {
    return new M7([ [ {
        nested: recordValue$prime
    } ] ]);
})();
var m7 = /* #__PURE__ */ (function () {
    return new M7([ [ {
        nested: recordValue
    } ] ]);
})();
var m6$prime = /* #__PURE__ */ (function () {
    return new M6(1, [ "a" ], [  ], [ [ "b" ] ], [ [ "c" ] ], [  ], recordValue$prime, {
        nested: recordValue$prime
    });
})();
var m6 = /* #__PURE__ */ (function () {
    return new M6(1, "a", [  ], [ "b" ], [ "c" ], [  ], recordValue, {
        nested: recordValue
    });
})();
var m5$prime = /* #__PURE__ */ (function () {
    return new M5({
        nested: recordValue$prime
    });
})();
var m5 = /* #__PURE__ */ (function () {
    return new M5({
        nested: recordValue
    });
})();
var m4$prime = /* #__PURE__ */ (function () {
    return new M4(recordValue$prime);
})();
var m4 = /* #__PURE__ */ (function () {
    return new M4(recordValue);
})();
var m3$prime = /* #__PURE__ */ (function () {
    return new M3([ [ "a" ], [ "b" ], [ "c" ] ]);
})();
var m3 = /* #__PURE__ */ (function () {
    return new M3([ "a", "b", "c" ]);
})();
var m2$prime = /* #__PURE__ */ (function () {
    return new M2(0);
})();
var m2 = /* #__PURE__ */ (function () {
    return new M2(0);
})();
var m1$prime = /* #__PURE__ */ (function () {
    return new M1([ "a" ], [ [ "b" ], [ "c" ] ]);
})();
var m1 = /* #__PURE__ */ (function () {
    return new M1("a", [ "b", "c" ]);
})();
var m0$prime = /* #__PURE__ */ (function () {
    return M0.value;
})();
var m0 = /* #__PURE__ */ (function () {
    return M0.value;
})();
var main = function __do() {
    Test_Assert["assert$prime"]("traverse - m0")(eq2(traverseStr1(m0))([ m0 ]))();
    Test_Assert["assert$prime"]("traverse - m1")(eq2(traverseStr1(m1))([ m1 ]))();
    Test_Assert["assert$prime"]("traverse - m2")(eq2(traverseStr1(m2))([ m2 ]))();
    Test_Assert["assert$prime"]("traverse - m3")(eq2(traverseStr1(m3))([ m3 ]))();
    Test_Assert["assert$prime"]("traverse - m4")(eq2(traverseStr1(m4))([ m4 ]))();
    Test_Assert["assert$prime"]("traverse - m5")(eq2(traverseStr1(m5))([ m5 ]))();
    Test_Assert["assert$prime"]("traverse - m6")(eq2(traverseStr1(m6))([ m6 ]))();
    Test_Assert["assert$prime"]("traverse - m7")(eq2(traverseStr1(m7))([ m7 ]))();
    Test_Assert["assert$prime"]("sequence - m0")(eq2(sequenceStr1(m0$prime))([ m0 ]))();
    Test_Assert["assert$prime"]("sequence - m1")(eq2(sequenceStr1(m1$prime))([ m1 ]))();
    Test_Assert["assert$prime"]("sequence - m2")(eq2(sequenceStr1(m2$prime))([ m2 ]))();
    Test_Assert["assert$prime"]("sequence - m3")(eq2(sequenceStr1(m3$prime))([ m3 ]))();
    Test_Assert["assert$prime"]("sequence - m4")(eq2(sequenceStr1(m4$prime))([ m4 ]))();
    Test_Assert["assert$prime"]("sequence - m5")(eq2(sequenceStr1(m5$prime))([ m5 ]))();
    Test_Assert["assert$prime"]("sequence - m6")(eq2(sequenceStr1(m6$prime))([ m6 ]))();
    Test_Assert["assert$prime"]("sequence - m7")(eq2(sequenceStr1(m7$prime))([ m7 ]))();
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
    traverseStr,
    sequenceStr,
    m0,
    m1,
    m2,
    m3,
    m4,
    m5,
    m6,
    m7,
    recordValue,
    m0$prime,
    m1$prime,
    m2$prime,
    m3$prime,
    m4$prime,
    m5$prime,
    m6$prime,
    m7$prime,
    recordValue$prime,
    main,
    eqM,
    functorM,
    foldableM,
    traversableM
};
