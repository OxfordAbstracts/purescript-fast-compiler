import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Apply from "../Control.Apply/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var $$void = /* #__PURE__ */ Data_Functor["void"](Effect.functorEffect);
var Sequence = /* #__PURE__ */ (function () {
    function Sequence(value0) {
        this.value0 = value0;
    };
    Sequence.create = function (value0) {
        return new Sequence(value0);
    };
    return Sequence;
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
var Nil = /* #__PURE__ */ (function () {
    function Nil() {

    };
    Nil.value = new Nil();
    return Nil;
})();
var sequenceListSeq = function (dictMonad) {
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    var Apply0 = (dictMonad.Bind1()).Apply0();
    var apply = Control_Apply.apply(Apply0);
    var map = Data_Functor.map(Apply0.Functor0());
    return function (v) {
        if (v instanceof Nil) {
            return pure(Nil.value);
        };
        if (v instanceof Cons) {
            return apply(map(Cons.create)(v.value0))(sequenceListSeq(dictMonad)(v.value1));
        };
        throw new Error("Failed pattern match at Main (line 14, column 1 - line 14, column 67): " + [ v.constructor.name ]);
    };
};
var sequenceList$prime$prime = /* #__PURE__ */ (function () {
    return new Sequence(function (dictMonad) {
        return sequenceListSeq(dictMonad);
    });
})();
var sequenceList = /* #__PURE__ */ (function () {
    return new Sequence(function (dictMonad) {
        return sequenceListSeq(dictMonad);
    });
})();
var sequence = function (v) {
    return function (dictMonad) {
        return v.value0(dictMonad);
    };
};
var sequenceList$prime = /* #__PURE__ */ (function () {
    return new Sequence(function (dictMonad) {
        var pure = Control_Applicative.pure(dictMonad.Applicative0());
        var Apply0 = (dictMonad.Bind1()).Apply0();
        var apply = Control_Apply.apply(Apply0);
        var map = Data_Functor.map(Apply0.Functor0());
        return function (val) {
            if (val instanceof Nil) {
                return pure(Nil.value);
            };
            if (val instanceof Cons) {
                return apply(map(Cons.create)(val.value0))(sequence(sequenceList$prime)(dictMonad)(val.value1));
            };
            throw new Error("Failed pattern match at Main (line 22, column 36 - line 24, column 56): " + [ val.constructor.name ]);
        };
    });
})();
var sequenceList$prime$prime$prime = /* #__PURE__ */ (function () {
    return new Sequence(function (dictMonad) {
        var pure = Control_Applicative.pure(dictMonad.Applicative0());
        var Apply0 = (dictMonad.Bind1()).Apply0();
        var apply = Control_Apply.apply(Apply0);
        var map = Data_Functor.map(Apply0.Functor0());
        return function (val) {
            if (val instanceof Nil) {
                return pure(Nil.value);
            };
            if (val instanceof Cons) {
                return apply(map(Cons.create)(val.value0))(sequence(sequenceList$prime$prime$prime)(dictMonad)(val.value1));
            };
            throw new Error("Failed pattern match at Main (line 30, column 38 - line 32, column 58): " + [ val.constructor.name ]);
        };
    });
})();
var main = function __do() {
    $$void(sequence(sequenceList)(Effect.monadEffect)(new Cons(Effect_Console.log("Done"), Nil.value)))();
    $$void(sequence(sequenceList$prime)(Effect.monadEffect)(new Cons(Effect_Console.log("Done"), Nil.value)))();
    $$void(sequence(sequenceList$prime$prime)(Effect.monadEffect)(new Cons(Effect_Console.log("Done"), Nil.value)))();
    return $$void(sequence(sequenceList$prime$prime$prime)(Effect.monadEffect)(new Cons(Effect_Console.log("Done"), Nil.value)))();
};
export {
    Cons,
    Nil,
    Sequence,
    sequence,
    sequenceListSeq,
    sequenceList,
    sequenceList$prime,
    sequenceList$prime$prime,
    sequenceList$prime$prime$prime,
    main
};
