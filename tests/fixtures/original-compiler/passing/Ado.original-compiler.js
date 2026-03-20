import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Apply from "../Control.Apply/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
var add = /* #__PURE__ */ Data_Semiring.add(Data_Semiring.semiringNumber);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var show1 = /* #__PURE__ */ Data_Show.show(/* #__PURE__ */ Data_Show.showArray(Data_Show.showInt));
var bindFlipped = /* #__PURE__ */ Control_Bind.bindFlipped(Effect.bindEffect);
var apply = /* #__PURE__ */ Control_Apply.apply(Effect.applyEffect);
var map = /* #__PURE__ */ Data_Functor.map(Effect.functorEffect);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var Nothing = /* #__PURE__ */ (function () {
    function Nothing() {

    };
    Nothing.value = new Nothing();
    return Nothing;
})();
var Just = /* #__PURE__ */ (function () {
    function Just(value0) {
        this.value0 = value0;
    };
    Just.create = function (value0) {
        return new Just(value0);
    };
    return Just;
})();
var test8 = function (dictApplicative) {
    var pure1 = Control_Applicative.pure(dictApplicative);
    return function (dictApplicative1) {
        var pure2 = Control_Applicative.pure(dictApplicative1);
        return function (v) {
            return pure1(pure2(1.0));
        };
    };
};
var test6 = function (dictApplicative) {
    var pure1 = Control_Applicative.pure(dictApplicative);
    return function (dictPartial) {
        return function (mx) {
            return function (v) {
                return pure1((function () {
                    var f = function (v1) {
                        if (v1 instanceof Just) {
                            return v1.value0;
                        };
                        throw new Error("Failed pattern match at Main (line 47, column 5 - line 47, column 32): " + [ v1.constructor.name ]);
                    };
                    return f(mx);
                })());
            };
        };
    };
};
var test5 = function (dictApply) {
    var apply2 = Control_Apply.apply(dictApply);
    var map2 = Data_Functor.map(dictApply.Functor0());
    return function (mx) {
        return function (my) {
            return function (mz) {
                return apply2(apply2(map2(function (v) {
                    return function (v1) {
                        var sum = v + v1;
                        return function (v2) {
                            return v2 + sum + 1.0;
                        };
                    };
                })(mx))(my))(mz);
            };
        };
    };
};
var test4 = function (dictApply) {
    var apply2 = Control_Apply.apply(dictApply);
    var map2 = Data_Functor.map(dictApply.Functor0());
    return function (mx) {
        return function (my) {
            return apply2(map2(function (v) {
                return function (v1) {
                    return v + v1 + 1.0;
                };
            })(mx))(my);
        };
    };
};
var test11 = function (dictApply) {
    var apply2 = Control_Apply.apply(dictApply);
    var map2 = Data_Functor.map(dictApply.Functor0());
    return function (dictApplicative) {
        var pure1 = Control_Applicative.pure(dictApplicative);
        return function (v) {
            return apply2(apply2(map2(function (v1) {
                return function (v2) {
                    return function (v3) {
                        return show(v1) + (v2 + show1(v3));
                    };
                };
            })(pure1(1)))(pure1("A")))(pure1([  ]));
        };
    };
};
var test10 = function (dictApplicative) {
    var pure1 = Control_Applicative.pure(dictApplicative);
    return function (v) {
        return pure1((function () {
            var g = function (x) {
                return f(x) / 2.0;
            };
            var f = function (x) {
                return g(x) * 3.0;
            };
            return f(10.0);
        })());
    };
};
var test1 = function (dictApplicative) {
    var pure1 = Control_Applicative.pure(dictApplicative);
    return function (v) {
        return pure1("abc");
    };
};
var main = function __do() {
    var r = Effect_Ref["new"]("X")();
    return bindFlipped(Effect_Console.log)(apply(apply(apply(map(function (v) {
        return function (v1) {
            return function (v2) {
                return function (v3) {
                    return v1 + (v2 + ("n" + v3));
                };
            };
        };
    })(Effect_Ref.write("D")(r)))(Effect_Ref.read(r)))(pure("o")))(pure("e")))();
};
var functorMaybe = {
    map: function (v) {
        return function (v1) {
            if (v1 instanceof Nothing) {
                return Nothing.value;
            };
            if (v1 instanceof Just) {
                return new Just(v(v1.value0));
            };
            throw new Error("Failed pattern match at Main (line 9, column 1 - line 11, column 30): " + [ v.constructor.name, v1.constructor.name ]);
        };
    }
};
var map1 = /* #__PURE__ */ Data_Functor.map(functorMaybe);
var applyMaybe = {
    apply: function (v) {
        return function (v1) {
            if (v instanceof Just && v1 instanceof Just) {
                return new Just(v.value0(v1.value0));
            };
            return Nothing.value;
        };
    },
    Functor0: function () {
        return functorMaybe;
    }
};
var apply1 = /* #__PURE__ */ Control_Apply.apply(applyMaybe);
var test2 = function (v) {
    return apply1(map1(function (v1) {
        return function (v2) {
            return v1 + v2;
        };
    })(new Just(1.0)))(new Just(2.0));
};
var test3 = function (v) {
    return apply1(map1(function (v1) {
        return function (v2) {
            return 2.0;
        };
    })(new Just(1.0)))(Nothing.value);
};
var test9 = function (v) {
    return apply1(map1(add)(new Just(1.0)))(new Just(2.0));
};
var applicativeMaybe = /* #__PURE__ */ (function () {
    return {
        pure: Just.create,
        Apply0: function () {
            return applyMaybe;
        }
    };
})();
export {
    Nothing,
    Just,
    test1,
    test2,
    test3,
    test4,
    test5,
    test6,
    test8,
    test9,
    test10,
    test11,
    main,
    functorMaybe,
    applyMaybe,
    applicativeMaybe
};
