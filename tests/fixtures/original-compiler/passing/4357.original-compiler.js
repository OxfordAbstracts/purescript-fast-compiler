import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Monoid_Additive from "../Data.Monoid.Additive/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var fold = /* #__PURE__ */ Data_Foldable.fold(Data_Foldable.foldableArray)(/* #__PURE__ */ Data_Monoid_Additive.monoidAdditive(Data_Semiring.semiringInt));
var Foo = /* #__PURE__ */ (function () {
    function Foo(value0) {
        this.value0 = value0;
    };
    Foo.create = function (value0) {
        return new Foo(value0);
    };
    return Foo;
})();
var Bar = /* #__PURE__ */ (function () {
    function Bar(value0) {
        this.value0 = value0;
    };
    Bar.create = function (value0) {
        return new Bar(value0);
    };
    return Bar;
})();
var test = function (v) {
    var v1 = function (v2) {
        if (Data_Boolean.otherwise) {
            var v3 = fold([  ]);
            return v3;
        };
        throw new Error("Failed pattern match at Main (line 24, column 1 - line 24, column 25): " + [ v.constructor.name ]);
    };
    if (v instanceof Data_Maybe.Just) {
        return v.value0;
    };
    return v1(true);
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var g = function (v) {
    var v1 = function (v2) {
        var v3 = function (v4) {
            if (Data_Boolean.otherwise) {
                return 42;
            };
            throw new Error("Failed pattern match at Main (line 12, column 1 - line 12, column 16): " + [ v.constructor.name ]);
        };
        if (v instanceof Foo) {
            return v.value0;
        };
        return v3(true);
    };
    if (v instanceof Bar) {
        return v.value0;
    };
    return v1(true);
};
export {
    Foo,
    Bar,
    g,
    test,
    main
};
