import * as Data_Functor_Contravariant from "../Data.Functor.Contravariant/index.js";
import * as Data_Predicate from "../Data.Predicate/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var cmap = /* #__PURE__ */ Data_Functor_Contravariant.cmap(Data_Predicate.contravariantPredicate);
var Test1 = /* #__PURE__ */ (function () {
    function Test1(value0) {
        this.value0 = value0;
    };
    Test1.create = function (value0) {
        return new Test1(value0);
    };
    return Test1;
})();
var Test2 = /* #__PURE__ */ (function () {
    function Test2(value0) {
        this.value0 = value0;
    };
    Test2.create = function (value0) {
        return new Test2(value0);
    };
    return Test2;
})();
var functorTest = {
    map: function (f) {
        return function (m) {
            if (m instanceof Test1) {
                return new Test1(cmap(cmap(f))(m.value0));
            };
            if (m instanceof Test2) {
                return new Test2({
                    x: cmap(function (v1) {
                        return {
                            y: cmap(f)(v1.y)
                        };
                    })(m.value0.x)
                });
            };
            throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ m.constructor.name ]);
        };
    }
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Test1,
    Test2,
    main,
    functorTest
};
