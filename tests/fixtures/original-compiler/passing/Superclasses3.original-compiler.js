import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Control_Monad from "../Control.Monad/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var $runtime_lazy = function (name, moduleName, init) {
    var state = 0;
    var val;
    return function (lineNumber) {
        if (state === 2) return val;
        if (state === 1) throw new ReferenceError(name + " was needed before it finished initializing (module " + moduleName + ", line " + lineNumber + ")", moduleName, lineNumber);
        state = 1;
        val = init();
        state = 2;
        return val;
    };
};
var add = /* #__PURE__ */ Data_Semiring.add(Data_Semiring.semiringNumber);
var discard = /* #__PURE__ */ Control_Bind.discard(Control_Bind.discardUnit);
var MTrace = /* #__PURE__ */ (function () {
    function MTrace(value0) {
        this.value0 = value0;
    };
    MTrace.create = function (value0) {
        return new MTrace(value0);
    };
    return MTrace;
})();
var testFunctor = function (dictMonad) {
    var map = Data_Functor.map(((dictMonad.Bind1()).Apply0()).Functor0());
    return function (n) {
        return map(add(1.0))(n);
    };
};
var tell = function (dict) {
    return dict.tell;
};
var test = function (dictMonad) {
    var discard1 = discard(dictMonad.Bind1());
    return function (dictMonadWriter) {
        var tell1 = tell(dictMonadWriter);
        return function (w) {
            return discard1(tell1(w))(function () {
                return discard1(tell1(w))(function () {
                    return tell1(w);
                });
            });
        };
    };
};
var runMTrace = function (v) {
    return v.value0;
};
var monadMTrace = {
    Applicative0: function () {
        return applicativeMTrace;
    },
    Bind1: function () {
        return bindMTrace;
    }
};
var bindMTrace = {
    bind: function (m) {
        return function (f) {
            return new MTrace(function __do() {
                var $21 = runMTrace(m)();
                return runMTrace(f($21))();
            });
        };
    },
    Apply0: function () {
        return $lazy_applyMTrace(0);
    }
};
var applicativeMTrace = {
    pure: /* #__PURE__ */ (function () {
        var $22 = Control_Applicative.pure(Effect.applicativeEffect);
        return function ($23) {
            return MTrace.create($22($23));
        };
    })(),
    Apply0: function () {
        return $lazy_applyMTrace(0);
    }
};
var $lazy_functorMTrace = /* #__PURE__ */ $runtime_lazy("functorMTrace", "Main", function () {
    return {
        map: Control_Monad.liftM1(monadMTrace)
    };
});
var $lazy_applyMTrace = /* #__PURE__ */ $runtime_lazy("applyMTrace", "Main", function () {
    return {
        apply: Control_Monad.ap(monadMTrace),
        Functor0: function () {
            return $lazy_functorMTrace(0);
        }
    };
});
var functorMTrace = /* #__PURE__ */ $lazy_functorMTrace(24);
var applyMTrace = /* #__PURE__ */ $lazy_applyMTrace(27);
var writerMTrace = {
    tell: function (s) {
        return new MTrace(Effect_Console.log(s));
    },
    Monad0: function () {
        return monadMTrace;
    }
};
var main = /* #__PURE__ */ runMTrace(/* #__PURE__ */ test(monadMTrace)(writerMTrace)("Done"));
export {
    tell,
    testFunctor,
    test,
    MTrace,
    runMTrace,
    main,
    functorMTrace,
    applyMTrace,
    applicativeMTrace,
    bindMTrace,
    monadMTrace,
    writerMTrace
};
