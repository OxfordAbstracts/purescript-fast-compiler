import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Bifunctor from "../Data.Bifunctor/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Profunctor from "../Data.Profunctor/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var MonoAndPro = function (x) {
    return x;
};
var Test3 = function (x) {
    return x;
};
var MonoAndBi = function (x) {
    return x;
};
var Test1 = function (x) {
    return x;
};
var Test4 = function (x) {
    return x;
};
var Test2 = function (x) {
    return x;
};
var profunctorMonoAndPro = {
    dimap: function (v) {
        return function (v1) {
            return function (v2) {
                return Test_Assert["assert$prime"]("Profunctor instance was used but the Functor instance was expected")(false);
            };
        };
    }
};
var profunctorExclusivelyPro = {
    dimap: function (f) {
        return function (g) {
            return function (m) {
                throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [  ]);
            };
        };
    }
};
var rmap = /* #__PURE__ */ Data_Profunctor.rmap(profunctorExclusivelyPro);
var functorTest4 = {
    map: function (f) {
        return function (m) {
            return rmap(f)(m);
        };
    }
};
var functorMonoAndPro = {
    map: function (f) {
        return function (m) {
            return m;
        };
    }
};
var map = /* #__PURE__ */ Data_Functor.map(functorMonoAndPro);
var functorTest3 = {
    map: function (f) {
        return function (m) {
            return map(f)(m);
        };
    }
};
var map1 = /* #__PURE__ */ Data_Functor.map(functorTest3);
var functorMonoAndBi = {
    map: function (f) {
        return function (m) {
            return m;
        };
    }
};
var map2 = /* #__PURE__ */ Data_Functor.map(functorMonoAndBi);
var functorTest1 = {
    map: function (f) {
        return function (m) {
            return map2(f)(m);
        };
    }
};
var bifunctorMonoAndBi = {
    bimap: function (v) {
        return function (v1) {
            return function (v2) {
                return Test_Assert["assert$prime"]("Bifunctor instance was used but the Functor instance was expected")(false);
            };
        };
    }
};
var bifunctorExclusivelyBi = {
    bimap: function (f) {
        return function (g) {
            return function (m) {
                throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [  ]);
            };
        };
    }
};
var rmap1 = /* #__PURE__ */ Data_Bifunctor.rmap(bifunctorExclusivelyBi);
var functorTest2 = {
    map: function (f) {
        return function (m) {
            return rmap1(f)(m);
        };
    }
};
var main = /* #__PURE__ */ (function () {
    var t = pure(Data_Unit.unit);
    var v = Data_Functor.map(functorTest1)(identity)(t);
    return function __do() {
        v();
        var t1 = pure(Data_Unit.unit);
        var v1 = map1(identity)(t1);
        v1();
        return Effect_Console.log("Done")();
    };
})();
export {
    MonoAndBi,
    Test1,
    Test2,
    MonoAndPro,
    Test3,
    Test4,
    main,
    functorMonoAndBi,
    bifunctorMonoAndBi,
    functorTest1,
    bifunctorExclusivelyBi,
    functorTest2,
    functorMonoAndPro,
    profunctorMonoAndPro,
    functorTest3,
    profunctorExclusivelyPro,
    functorTest4
};
