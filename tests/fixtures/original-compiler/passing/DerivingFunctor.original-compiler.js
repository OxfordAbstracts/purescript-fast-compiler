import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Tuple from "../Data.Tuple/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorFn);
var map1 = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var map2 = /* #__PURE__ */ Data_Functor.map(Data_Tuple.functorTuple);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var eqRec = /* #__PURE__ */ Data_Eq.eqRec();
var eqRowCons = /* #__PURE__ */ Data_Eq.eqRowCons(Data_Eq.eqRowNil)();
var eqArray = /* #__PURE__ */ Data_Eq.eqArray(Data_Eq.eqString);
var eqTuple = /* #__PURE__ */ Data_Tuple.eqTuple(Data_Eq.eqInt);
var eqArray1 = /* #__PURE__ */ Data_Eq.eqArray(Data_Eq.eqInt);
var eq2 = /* #__PURE__ */ Data_Eq.eq(eqArray1);
var T = /* #__PURE__ */ (function () {
    function T(value0) {
        this.value0 = value0;
    };
    T.create = function (value0) {
        return new T(value0);
    };
    return T;
})();
var M0 = /* #__PURE__ */ (function () {
    function M0(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    M0.create = function (value0) {
        return function (value1) {
            return new M0(value0, value1);
        };
    };
    return M0;
})();
var M1 = /* #__PURE__ */ (function () {
    function M1(value0) {
        this.value0 = value0;
    };
    M1.create = function (value0) {
        return new M1(value0);
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
    function M5(value0, value1, value2, value3, value4, value5, value6, value7) {
        this.value0 = value0;
        this.value1 = value1;
        this.value2 = value2;
        this.value3 = value3;
        this.value4 = value4;
        this.value5 = value5;
        this.value6 = value6;
        this.value7 = value7;
    };
    M5.create = function (value0) {
        return function (value1) {
            return function (value2) {
                return function (value3) {
                    return function (value4) {
                        return function (value5) {
                            return function (value6) {
                                return function (value7) {
                                    return new M5(value0, value1, value2, value3, value4, value5, value6, value7);
                                };
                            };
                        };
                    };
                };
            };
        };
    };
    return M5;
})();
var M6 = /* #__PURE__ */ (function () {
    function M6(value0) {
        this.value0 = value0;
    };
    M6.create = function (value0) {
        return new M6(value0);
    };
    return M6;
})();
var Fun3 = /* #__PURE__ */ (function () {
    function Fun3(value0) {
        this.value0 = value0;
    };
    Fun3.create = function (value0) {
        return new Fun3(value0);
    };
    return Fun3;
})();
var Fun2 = /* #__PURE__ */ (function () {
    function Fun2(value0) {
        this.value0 = value0;
    };
    Fun2.create = function (value0) {
        return new Fun2(value0);
    };
    return Fun2;
})();
var Fun1 = /* #__PURE__ */ (function () {
    function Fun1(value0) {
        this.value0 = value0;
    };
    Fun1.create = function (value0) {
        return new Fun1(value0);
    };
    return Fun1;
})();
var functorFun3 = function (dictFunctor) {
    var map4 = Data_Functor.map(dictFunctor);
    return {
        map: function (f) {
            return function (m) {
                return new Fun3(map(map1(map4(map1(function (v1) {
                    return {
                        nested: {
                            arrayIgnore: v1.nested.arrayIgnore,
                            empty: v1.nested.empty,
                            fIgnore: v1.nested.fIgnore,
                            ignore: v1.nested.ignore,
                            a: f(v1.nested.a),
                            fa: map4(f)(v1.nested.fa),
                            recursiveA: map1(map2(map1(f)))(v1.nested.recursiveA),
                            zArrayA: map1(f)(v1.nested.zArrayA)
                        }
                    };
                }))))(m.value0));
            };
        }
    };
};
var functorFun2 = {
    map: function (f) {
        return function (m) {
            return new Fun2(map(map(map1(map1(f))))(m.value0));
        };
    }
};
var functorFun1 = {
    map: function (f) {
        return function (m) {
            return new Fun1(map(map(f))(m.value0));
        };
    }
};
var recordValueR = /* #__PURE__ */ (function () {
    return {
        a: "71",
        zArrayA: [ "72" ],
        fa: [ "73" ],
        ignore: 91,
        recursiveA: [ new Data_Tuple.Tuple(1, [ "1" ]), new Data_Tuple.Tuple(2, [ "2" ]) ],
        arrayIgnore: [ 92, 93 ],
        fIgnore: [ 94 ],
        empty: {}
    };
})();
var recordValueL = /* #__PURE__ */ (function () {
    return {
        a: 71,
        zArrayA: [ 72 ],
        fa: [ 73 ],
        ignore: 91,
        recursiveA: [ new Data_Tuple.Tuple(1, [ 1 ]), new Data_Tuple.Tuple(2, [ 2 ]) ],
        arrayIgnore: [ 92, 93 ],
        fIgnore: [ 94 ],
        empty: {}
    };
})();
var m6R = /* #__PURE__ */ (function () {
    return new M6([ [ [ "1", "2" ] ] ]);
})();
var m6L = /* #__PURE__ */ (function () {
    return new M6([ [ [ 1, 2 ] ] ]);
})();
var m5R = /* #__PURE__ */ (function () {
    return new M5(0, "1", [ 2, 3 ], [ "3", "4" ], [ "5", "6" ], [ 7, 8 ], recordValueR, {
        nested: recordValueR
    });
})();
var m5L = /* #__PURE__ */ (function () {
    return new M5(0, 1, [ 2, 3 ], [ 3, 4 ], [ 5, 6 ], [ 7, 8 ], recordValueL, {
        nested: recordValueL
    });
})();
var m4R = /* #__PURE__ */ (function () {
    return new M4({
        nested: recordValueR
    });
})();
var m4L = /* #__PURE__ */ (function () {
    return new M4({
        nested: recordValueL
    });
})();
var m3R = /* #__PURE__ */ (function () {
    return new M3(recordValueR);
})();
var m3L = /* #__PURE__ */ (function () {
    return new M3(recordValueL);
})();
var m2R = /* #__PURE__ */ (function () {
    return new M2([ "0", "1" ]);
})();
var m2L = /* #__PURE__ */ (function () {
    return new M2([ 0, 1 ]);
})();
var m1R = /* #__PURE__ */ (function () {
    return new M1(0);
})();
var m1L = /* #__PURE__ */ (function () {
    return new M1(0);
})();
var m0R = /* #__PURE__ */ (function () {
    return new M0("0", [ "1", "2" ]);
})();
var m0L = /* #__PURE__ */ (function () {
    return new M0(0, [ 1, 2 ]);
})();
var functorT = {
    map: function (f) {
        return function (m) {
            return new T(function (dictShow) {
                return map(f)(m.value0(dictShow));
            });
        };
    }
};
var taTests = /* #__PURE__ */ (function () {
    var v = Data_Functor.map(functorT)(show)(new T(function (dictShow) {
        return function (v1) {
            return 42;
        };
    }));
    return Test_Assert["assert$prime"]("map show T")(v.value0(Data_Show.showString)("hello") === "42");
})();
var functorM = function (dictFunctor) {
    var map4 = Data_Functor.map(dictFunctor);
    return {
        map: function (f) {
            return function (m) {
                if (m instanceof M0) {
                    return new M0(f(m.value0), map1(f)(m.value1));
                };
                if (m instanceof M1) {
                    return new M1(m.value0);
                };
                if (m instanceof M2) {
                    return new M2(map4(f)(m.value0));
                };
                if (m instanceof M3) {
                    return new M3({
                        ignore: m.value0.ignore,
                        arrayIgnore: m.value0.arrayIgnore,
                        fIgnore: m.value0.fIgnore,
                        empty: m.value0.empty,
                        a: f(m.value0.a),
                        fa: map4(f)(m.value0.fa),
                        recursiveA: map1(map2(map1(f)))(m.value0.recursiveA),
                        zArrayA: map1(f)(m.value0.zArrayA)
                    });
                };
                if (m instanceof M4) {
                    return new M4({
                        nested: {
                            ignore: m.value0.nested.ignore,
                            arrayIgnore: m.value0.nested.arrayIgnore,
                            fIgnore: m.value0.nested.fIgnore,
                            empty: m.value0.nested.empty,
                            a: f(m.value0.nested.a),
                            fa: map4(f)(m.value0.nested.fa),
                            recursiveA: map1(map2(map1(f)))(m.value0.nested.recursiveA),
                            zArrayA: map1(f)(m.value0.nested.zArrayA)
                        }
                    });
                };
                if (m instanceof M5) {
                    return new M5(m.value0, f(m.value1), m.value2, map1(f)(m.value3), map4(f)(m.value4), m.value5, {
                        ignore: m.value6.ignore,
                        arrayIgnore: m.value6.arrayIgnore,
                        fIgnore: m.value6.fIgnore,
                        empty: m.value6.empty,
                        a: f(m.value6.a),
                        fa: map4(f)(m.value6.fa),
                        recursiveA: map1(map2(map1(f)))(m.value6.recursiveA),
                        zArrayA: map1(f)(m.value6.zArrayA)
                    }, {
                        nested: {
                            ignore: m.value7.nested.ignore,
                            arrayIgnore: m.value7.nested.arrayIgnore,
                            fIgnore: m.value7.nested.fIgnore,
                            empty: m.value7.nested.empty,
                            a: f(m.value7.nested.a),
                            fa: map4(f)(m.value7.nested.fa),
                            recursiveA: map1(map2(map1(f)))(m.value7.nested.recursiveA),
                            zArrayA: map1(f)(m.value7.nested.zArrayA)
                        }
                    });
                };
                if (m instanceof M6) {
                    return new M6(map1(map1(map1(f)))(m.value0));
                };
                throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
            };
        }
    };
};
var map3 = /* #__PURE__ */ Data_Functor.map(/* #__PURE__ */ functorM(Data_Functor.functorArray));
var f3Test = /* #__PURE__ */ Test_Assert["assert$prime"]("map - Fun3")(/* #__PURE__ */ (function () {
    var right = function (v) {
        return [ [ [ {
            nested: recordValueR
        } ] ] ];
    };
    var left = function (v) {
        return [ [ [ {
            nested: recordValueL
        } ] ] ];
    };
    var v = Data_Functor.map(functorFun3(Data_Functor.functorArray))(show)(new Fun3(left));
    return Data_Eq.eq(Data_Eq.eqArray(Data_Eq.eqArray(Data_Eq.eqArray(eqRec(eqRowCons({
        reflectSymbol: function () {
            return "nested";
        }
    })(eqRec(Data_Eq.eqRowCons(Data_Eq.eqRowCons(Data_Eq.eqRowCons(Data_Eq.eqRowCons(Data_Eq.eqRowCons(Data_Eq.eqRowCons(Data_Eq.eqRowCons(eqRowCons({
        reflectSymbol: function () {
            return "zArrayA";
        }
    })(eqArray))()({
        reflectSymbol: function () {
            return "recursiveA";
        }
    })(Data_Eq.eqArray(eqTuple(eqArray))))()({
        reflectSymbol: function () {
            return "ignore";
        }
    })(Data_Eq.eqInt))()({
        reflectSymbol: function () {
            return "fa";
        }
    })(eqArray))()({
        reflectSymbol: function () {
            return "fIgnore";
        }
    })(eqArray1))()({
        reflectSymbol: function () {
            return "empty";
        }
    })(eqRec(Data_Eq.eqRowNil)))()({
        reflectSymbol: function () {
            return "arrayIgnore";
        }
    })(eqArray1))()({
        reflectSymbol: function () {
            return "a";
        }
    })(Data_Eq.eqString))))))))(v.value0(Data_Unit.unit))(right(Data_Unit.unit));
})());
var f2Test = /* #__PURE__ */ Test_Assert["assert$prime"]("map - Fun2")(/* #__PURE__ */ (function () {
    var left = function (a) {
        return function (b) {
            return [ [ a + b | 0 ] ];
        };
    };
    var fn1 = Data_Show.show(Data_Show.showInt);
    var right = function (a) {
        return function (b) {
            return map1(map1(fn1))(left(a)(b));
        };
    };
    var v = Data_Functor.map(functorFun2)(fn1)(new Fun2(left));
    return Data_Eq.eq(Data_Eq.eqArray(eqArray))(v.value0(1)(2))(right(1)(2));
})());
var f1Test = /* #__PURE__ */ Test_Assert["assert$prime"]("map - Fun1")(/* #__PURE__ */ (function () {
    var left = function (a) {
        return function (b) {
            return a + b | 0;
        };
    };
    var fn1 = Data_Show.show(Data_Show.showInt);
    var right = function (a) {
        return function (b) {
            return fn1(left(a)(b));
        };
    };
    var v = Data_Functor.map(functorFun1)(fn1)(new Fun1(left));
    return v.value0(1)(2) === right(1)(2);
})());
var funTests = function __do() {
    f1Test();
    f2Test();
    f3Test();
    return taTests();
};
var eqM = function (dictEq1) {
    var eq11 = Data_Eq.eq1(dictEq1);
    var eq12 = eq11(Data_Eq.eqInt);
    return function (dictEq) {
        var eq4 = Data_Eq.eq(dictEq);
        var eqArray2 = Data_Eq.eqArray(dictEq);
        var eq5 = Data_Eq.eq(eqArray2);
        var eq13 = eq11(dictEq);
        var eq6 = Data_Eq.eq(Data_Eq.eqArray(eqTuple(eqArray2)));
        var eq7 = Data_Eq.eq(Data_Eq.eqArray(Data_Eq.eqArray(eqArray2)));
        return {
            eq: function (x) {
                return function (y) {
                    if (x instanceof M0 && y instanceof M0) {
                        return eq4(x.value0)(y.value0) && eq5(x.value1)(y.value1);
                    };
                    if (x instanceof M1 && y instanceof M1) {
                        return x.value0 === y.value0;
                    };
                    if (x instanceof M2 && y instanceof M2) {
                        return eq13(x.value0)(y.value0);
                    };
                    if (x instanceof M3 && y instanceof M3) {
                        return eq4(x.value0.a)(y.value0.a) && eq2(x.value0.arrayIgnore)(y.value0.arrayIgnore) && true && eq12(x.value0.fIgnore)(y.value0.fIgnore) && eq13(x.value0.fa)(y.value0.fa) && x.value0.ignore === y.value0.ignore && eq6(x.value0.recursiveA)(y.value0.recursiveA) && eq5(x.value0.zArrayA)(y.value0.zArrayA);
                    };
                    if (x instanceof M4 && y instanceof M4) {
                        return eq4(x.value0.nested.a)(y.value0.nested.a) && eq2(x.value0.nested.arrayIgnore)(y.value0.nested.arrayIgnore) && true && eq12(x.value0.nested.fIgnore)(y.value0.nested.fIgnore) && eq13(x.value0.nested.fa)(y.value0.nested.fa) && x.value0.nested.ignore === y.value0.nested.ignore && eq6(x.value0.nested.recursiveA)(y.value0.nested.recursiveA) && eq5(x.value0.nested.zArrayA)(y.value0.nested.zArrayA);
                    };
                    if (x instanceof M5 && y instanceof M5) {
                        return x.value0 === y.value0 && eq4(x.value1)(y.value1) && eq2(x.value2)(y.value2) && eq5(x.value3)(y.value3) && eq13(x.value4)(y.value4) && eq12(x.value5)(y.value5) && (eq4(x.value6.a)(y.value6.a) && eq2(x.value6.arrayIgnore)(y.value6.arrayIgnore) && true && eq12(x.value6.fIgnore)(y.value6.fIgnore) && eq13(x.value6.fa)(y.value6.fa) && x.value6.ignore === y.value6.ignore && eq6(x.value6.recursiveA)(y.value6.recursiveA) && eq5(x.value6.zArrayA)(y.value6.zArrayA)) && (eq4(x.value7.nested.a)(y.value7.nested.a) && eq2(x.value7.nested.arrayIgnore)(y.value7.nested.arrayIgnore) && true && eq12(x.value7.nested.fIgnore)(y.value7.nested.fIgnore) && eq13(x.value7.nested.fa)(y.value7.nested.fa) && x.value7.nested.ignore === y.value7.nested.ignore && eq6(x.value7.nested.recursiveA)(y.value7.nested.recursiveA) && eq5(x.value7.nested.zArrayA)(y.value7.nested.zArrayA));
                    };
                    if (x instanceof M6 && y instanceof M6) {
                        return eq7(x.value0)(y.value0);
                    };
                    return false;
                };
            }
        };
    };
};
var eq3 = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ eqM(Data_Eq.eq1Array)(Data_Eq.eqString));
var maTests = function __do() {
    Test_Assert["assert$prime"]("map - M0")(eq3(map3(show)(m0L))(m0R))();
    Test_Assert["assert$prime"]("map - M1")(eq3(map3(show)(m1L))(m1R))();
    Test_Assert["assert$prime"]("map - M2")(eq3(map3(show)(m2L))(m2R))();
    Test_Assert["assert$prime"]("map - M3")(eq3(map3(show)(m3L))(m3R))();
    Test_Assert["assert$prime"]("map - M4")(eq3(map3(show)(m4L))(m4R))();
    Test_Assert["assert$prime"]("map - M5")(eq3(map3(show)(m5L))(m5R))();
    return Test_Assert["assert$prime"]("map - M6")(eq3(map3(show)(m6L))(m6R))();
};
var main = function __do() {
    maTests();
    funTests();
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
    m0L,
    m0R,
    m1L,
    m1R,
    m2L,
    m2R,
    m3L,
    m3R,
    m4L,
    m4R,
    m5L,
    m5R,
    recordValueL,
    recordValueR,
    m6L,
    m6R,
    maTests,
    Fun1,
    f1Test,
    Fun2,
    f2Test,
    Fun3,
    f3Test,
    T,
    taTests,
    funTests,
    main,
    eqM,
    functorM,
    functorFun1,
    functorFun2,
    functorFun3,
    functorT
};
