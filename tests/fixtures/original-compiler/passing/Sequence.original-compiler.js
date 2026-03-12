import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Apply from "../Control.Apply/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
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
var Nil = /* #__PURE__ */ (function () {
    function Nil() {

    };
    Nil.value = new Nil();
    return Nil;
})();
var sequence = function (dict) {
    return dict.sequence;
};
var sequenceList = {
    sequence: function (dictMonad) {
        var pure = Control_Applicative.pure(dictMonad.Applicative0());
        var Apply0 = (dictMonad.Bind1()).Apply0();
        var apply = Control_Apply.apply(Apply0);
        var map = Data_Functor.map(Apply0.Functor0());
        return function (v) {
            if (v instanceof Nil) {
                return pure(Nil.value);
            };
            if (v instanceof Cons) {
                return apply(map(Cons.create)(v.value0))(sequence(sequenceList)(dictMonad)(v.value1));
            };
            throw new Error("Failed pattern match at Main (line 12, column 1 - line 14, column 52): " + [ v.constructor.name ]);
        };
    }
};
var main = /* #__PURE__ */ (function () {
    return sequence(sequenceList)(Effect.monadEffect)(new Cons(Effect_Console.log("Done"), Nil.value));
})();
export {
    sequence,
    Cons,
    Nil,
    main,
    sequenceList
};
