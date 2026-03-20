import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Apply from "../Control.Apply/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Bifoldable from "../Data.Bifoldable/index.js";
import * as Data_Bifunctor from "../Data.Bifunctor/index.js";
import * as Data_Bitraversable from "../Data.Bitraversable/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Functor_Contravariant from "../Data.Functor.Contravariant/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Data_Predicate from "../Data.Predicate/index.js";
import * as Data_Profunctor from "../Data.Profunctor/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Traversable from "../Data.Traversable/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var lmap = /* #__PURE__ */ Data_Bifunctor.lmap(Data_Bifunctor.bifunctorTuple);
var cmap = /* #__PURE__ */ Data_Functor_Contravariant.cmap(Data_Predicate.contravariantPredicate);
var lcmap = /* #__PURE__ */ Data_Profunctor.lcmap(Data_Profunctor.profunctorFn);
var foldl = /* #__PURE__ */ Data_Foldable.foldl(Data_Foldable.foldableArray);
var bifoldl = /* #__PURE__ */ Data_Bifoldable.bifoldl(Data_Bifoldable.bifoldableTuple);
var foldr = /* #__PURE__ */ Data_Foldable.foldr(Data_Foldable.foldableArray);
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var bifoldr = /* #__PURE__ */ Data_Bifoldable.bifoldr(Data_Bifoldable.bifoldableTuple);
var foldMap = /* #__PURE__ */ Data_Foldable.foldMap(Data_Foldable.foldableArray);
var bifoldMap = /* #__PURE__ */ Data_Bifoldable.bifoldMap(Data_Bifoldable.bifoldableTuple);
var traverse = /* #__PURE__ */ Data_Traversable.traverse(Data_Traversable.traversableArray);
var ltraverse = /* #__PURE__ */ Data_Bitraversable.ltraverse(Data_Bitraversable.bitraversableTuple);
var Test0 = /* #__PURE__ */ (function () {
    function Test0() {

    };
    Test0.value = new Test0();
    return Test0;
})();
var Test1 = /* #__PURE__ */ (function () {
    function Test1(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Test1.create = function (value0) {
        return function (value1) {
            return new Test1(value0, value1);
        };
    };
    return Test1;
})();
var Test2 = /* #__PURE__ */ (function () {
    function Test2(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Test2.create = function (value0) {
        return function (value1) {
            return new Test2(value0, value1);
        };
    };
    return Test2;
})();
var Test3 = /* #__PURE__ */ (function () {
    function Test3(value0, value1, value2, value3) {
        this.value0 = value0;
        this.value1 = value1;
        this.value2 = value2;
        this.value3 = value3;
    };
    Test3.create = function (value0) {
        return function (value1) {
            return function (value2) {
                return function (value3) {
                    return new Test3(value0, value1, value2, value3);
                };
            };
        };
    };
    return Test3;
})();
var Test4 = /* #__PURE__ */ (function () {
    function Test4(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Test4.create = function (value0) {
        return function (value1) {
            return new Test4(value0, value1);
        };
    };
    return Test4;
})();
var Test5 = /* #__PURE__ */ (function () {
    function Test5(value0) {
        this.value0 = value0;
    };
    Test5.create = function (value0) {
        return new Test5(value0);
    };
    return Test5;
})();
var FromProAndContra = /* #__PURE__ */ (function () {
    function FromProAndContra(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    FromProAndContra.create = function (value0) {
        return function (value1) {
            return new FromProAndContra(value0, value1);
        };
    };
    return FromProAndContra;
})();
var bifunctorTest = function (dictBifunctor) {
    var bimap = Data_Bifunctor.bimap(dictBifunctor);
    var lmap1 = Data_Bifunctor.lmap(dictBifunctor);
    var rmap = Data_Bifunctor.rmap(dictBifunctor);
    return {
        bimap: function (f) {
            return function (g) {
                return function (m) {
                    if (m instanceof Test0) {
                        return Test0.value;
                    };
                    if (m instanceof Test1) {
                        return new Test1(map(f)(m.value0), g(m.value1));
                    };
                    if (m instanceof Test2) {
                        return new Test2(m.value0, m.value1);
                    };
                    if (m instanceof Test3) {
                        return new Test3(m.value0, bimap(f)(g)(m.value1), lmap1(f)(m.value2), rmap(g)(m.value3));
                    };
                    if (m instanceof Test4) {
                        return new Test4(map(lmap(f))(m.value0), lmap(g)(m.value1));
                    };
                    if (m instanceof Test5) {
                        return new Test5({
                            nested: map(function (v1) {
                                return {
                                    x: bimap(function (v2) {
                                        return {
                                            a: f(v2.a)
                                        };
                                    })(function (v2) {
                                        return {
                                            b: g(v2.b)
                                        };
                                    })(v1.x)
                                };
                            })(m.value0.nested)
                        });
                    };
                    throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
                };
            };
        }
    };
};
var bifunctorFromProAndContra = {
    bimap: function (f) {
        return function (g) {
            return function (m) {
                return new FromProAndContra(cmap(lcmap(f))(m.value0), lcmap(cmap(g))(m.value1));
            };
        };
    }
};
var bifoldableTest = function (dictBifoldable) {
    var bifoldl1 = Data_Bifoldable.bifoldl(dictBifoldable);
    var bifoldr1 = Data_Bifoldable.bifoldr(dictBifoldable);
    var bifoldMap1 = Data_Bifoldable.bifoldMap(dictBifoldable);
    return {
        bifoldl: function (f) {
            return function (g) {
                return function (z) {
                    return function (m) {
                        if (m instanceof Test0) {
                            return z;
                        };
                        if (m instanceof Test1) {
                            return g(foldl(f)(z)(m.value0))(m.value1);
                        };
                        if (m instanceof Test2) {
                            return z;
                        };
                        if (m instanceof Test3) {
                            return bifoldl1(Data_Function["const"])(g)(Data_Function.flip(bifoldl1)(Data_Function["const"])(f)(bifoldl1(f)(g)(z)(m.value1))(m.value2))(m.value3);
                        };
                        if (m instanceof Test4) {
                            return Data_Function.flip(bifoldl)(Data_Function["const"])(g)(foldl(Data_Function.flip(bifoldl)(Data_Function["const"])(f))(z)(m.value0))(m.value1);
                        };
                        if (m instanceof Test5) {
                            return foldl(function (v1) {
                                return function (v2) {
                                    return bifoldl1(function (v3) {
                                        return function (v4) {
                                            return f(v3)(v4.a);
                                        };
                                    })(function (v3) {
                                        return function (v4) {
                                            return g(v3)(v4.b);
                                        };
                                    })(v1)(v2.x);
                                };
                            })(z)(m.value0.nested);
                        };
                        throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
                    };
                };
            };
        },
        bifoldr: function (f) {
            return function (g) {
                return function (z) {
                    return function (m) {
                        if (m instanceof Test0) {
                            return z;
                        };
                        if (m instanceof Test1) {
                            return foldr(f)(g(m.value1)(z))(m.value0);
                        };
                        if (m instanceof Test2) {
                            return z;
                        };
                        if (m instanceof Test3) {
                            return bifoldr1(f)(g)(Data_Function.flip(bifoldr1)(Data_Function["const"](identity))(f)(bifoldr1(Data_Function["const"](identity))(g)(z)(m.value3))(m.value2))(m.value1);
                        };
                        if (m instanceof Test4) {
                            return foldr(Data_Function.flip(Data_Function.flip(bifoldr)(Data_Function["const"](identity))(f)))(Data_Function.flip(bifoldr)(Data_Function["const"](identity))(g)(z)(m.value1))(m.value0);
                        };
                        if (m instanceof Test5) {
                            return foldr(function (v1) {
                                return function (v2) {
                                    return bifoldr1(function (v3) {
                                        return function (v4) {
                                            return f(v3.a)(v4);
                                        };
                                    })(function (v3) {
                                        return function (v4) {
                                            return g(v3.b)(v4);
                                        };
                                    })(v2)(v1.x);
                                };
                            })(z)(m.value0.nested);
                        };
                        throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
                    };
                };
            };
        },
        bifoldMap: function (dictMonoid) {
            var mempty = Data_Monoid.mempty(dictMonoid);
            var append = Data_Semigroup.append(dictMonoid.Semigroup0());
            var foldMap1 = foldMap(dictMonoid);
            var bifoldMap2 = bifoldMap1(dictMonoid);
            var mempty1 = Data_Monoid.mempty(Data_Monoid.monoidFn(dictMonoid));
            var bifoldMap3 = bifoldMap(dictMonoid);
            return function (f) {
                return function (g) {
                    return function (m) {
                        if (m instanceof Test0) {
                            return mempty;
                        };
                        if (m instanceof Test1) {
                            return append(foldMap1(f)(m.value0))(g(m.value1));
                        };
                        if (m instanceof Test2) {
                            return mempty;
                        };
                        if (m instanceof Test3) {
                            return append(bifoldMap2(f)(g)(m.value1))(append(Data_Function.flip(bifoldMap2)(mempty1)(f)(m.value2))(bifoldMap2(mempty1)(g)(m.value3)));
                        };
                        if (m instanceof Test4) {
                            return append(foldMap1(Data_Function.flip(bifoldMap3)(mempty1)(f))(m.value0))(Data_Function.flip(bifoldMap3)(mempty1)(g)(m.value1));
                        };
                        if (m instanceof Test5) {
                            return foldMap1(function (v1) {
                                return bifoldMap2(function (v2) {
                                    return f(v2.a);
                                })(function (v2) {
                                    return g(v2.b);
                                })(v1.x);
                            })(m.value0.nested);
                        };
                        throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
                    };
                };
            };
        }
    };
};
var bitraversableTest = function (dictBitraversable) {
    var bitraverse = Data_Bitraversable.bitraverse(dictBitraversable);
    var ltraverse1 = Data_Bitraversable.ltraverse(dictBitraversable);
    var rtraverse = Data_Bitraversable.rtraverse(dictBitraversable);
    var bifunctorTest1 = bifunctorTest(dictBitraversable.Bifunctor0());
    var bifoldableTest1 = bifoldableTest(dictBitraversable.Bifoldable1());
    return {
        bitraverse: function (dictApplicative) {
            var pure = Control_Applicative.pure(dictApplicative);
            var Apply0 = dictApplicative.Apply0();
            var apply = Control_Apply.apply(Apply0);
            var map1 = Data_Functor.map(Apply0.Functor0());
            var traverse1 = traverse(dictApplicative);
            var bitraverse1 = bitraverse(dictApplicative);
            var ltraverse2 = ltraverse1(dictApplicative);
            var rtraverse1 = rtraverse(dictApplicative);
            var ltraverse3 = ltraverse(dictApplicative);
            return function (f) {
                return function (g) {
                    return function (m) {
                        if (m instanceof Test0) {
                            return pure(Test0.value);
                        };
                        if (m instanceof Test1) {
                            return apply(map1(function (v2) {
                                return function (v3) {
                                    return new Test1(v2, v3);
                                };
                            })(traverse1(f)(m.value0)))(g(m.value1));
                        };
                        if (m instanceof Test2) {
                            return pure(new Test2(m.value0, m.value1));
                        };
                        if (m instanceof Test3) {
                            return apply(apply(map1(function (v4) {
                                return function (v5) {
                                    return function (v6) {
                                        return new Test3(m.value0, v4, v5, v6);
                                    };
                                };
                            })(bitraverse1(f)(g)(m.value1)))(ltraverse2(f)(m.value2)))(rtraverse1(g)(m.value3));
                        };
                        if (m instanceof Test4) {
                            return apply(map1(function (v2) {
                                return function (v3) {
                                    return new Test4(v2, v3);
                                };
                            })(traverse1(ltraverse3(f))(m.value0)))(ltraverse3(g)(m.value1));
                        };
                        if (m instanceof Test5) {
                            return map1(function (v1) {
                                return new Test5({
                                    nested: v1
                                });
                            })(traverse1(function (v1) {
                                return map1(function (v2) {
                                    return {
                                        x: v2
                                    };
                                })(bitraverse1(function (v2) {
                                    return map1(function (v3) {
                                        return {
                                            a: v3
                                        };
                                    })(f(v2.a));
                                })(function (v2) {
                                    return map1(function (v3) {
                                        return {
                                            b: v3
                                        };
                                    })(g(v2.b));
                                })(v1.x));
                            })(m.value0.nested));
                        };
                        throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
                    };
                };
            };
        },
        bisequence: function (dictApplicative) {
            return function (v) {
                return Data_Bitraversable.bitraverse(bitraversableTest(dictBitraversable))(dictApplicative)(identity)(identity)(v);
            };
        },
        Bifunctor0: function () {
            return bifunctorTest1;
        },
        Bifoldable1: function () {
            return bifoldableTest1;
        }
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Test0,
    Test1,
    Test2,
    Test3,
    Test4,
    Test5,
    FromProAndContra,
    main,
    bifunctorTest,
    bifoldableTest,
    bitraversableTest,
    bifunctorFromProAndContra
};
