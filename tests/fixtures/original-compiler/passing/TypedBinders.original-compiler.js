import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Control_Monad from "../Control.Monad/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
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
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupString);
var Tuple = /* #__PURE__ */ (function () {
    function Tuple(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Tuple.create = function (value0) {
        return function (value1) {
            return new Tuple(value0, value1);
        };
    };
    return Tuple;
})();
var State = /* #__PURE__ */ (function () {
    function State(value0) {
        this.value0 = value0;
    };
    State.create = function (value0) {
        return new State(value0);
    };
    return State;
})();
var test5 = function (v) {
    return v;
};
var test4 = function (v) {
    return new Tuple(v.value1, v.value0);
};
var test3 = function (n) {
    if (n === 0) {
        return true;
    };
    return false;
};
var test2 = function (v) {
    return v(10);
};
var runState = function (s) {
    return function (v) {
        return v.value0(s);
    };
};
var put = function (dict) {
    return dict.put;
};
var monadStateState = /* #__PURE__ */ (function () {
    return {
        get: new State(function (s) {
            return new Tuple(s, s);
        }),
        put: function (s) {
            return new State(function (v) {
                return new Tuple(s, Data_Unit.unit);
            });
        }
    };
})();
var get = function (dict) {
    return dict.get;
};
var get1 = /* #__PURE__ */ get(monadStateState);
var modify = function (dictMonad) {
    var bind1 = Control_Bind.bind(dictMonad.Bind1());
    return function (dictMonadState) {
        var get2 = get(dictMonadState);
        var put1 = put(dictMonadState);
        return function (f) {
            return bind1(get2)(function (s) {
                return put1(f(s));
            });
        };
    };
};
var monadState = {
    Applicative0: function () {
        return applicativeState;
    },
    Bind1: function () {
        return bindState;
    }
};
var bindState = {
    bind: function (f) {
        return function (g) {
            return new State(function (s) {
                var v = runState(s)(f);
                return runState(v.value0)(g(v.value1));
            });
        };
    },
    Apply0: function () {
        return $lazy_applyState(0);
    }
};
var applicativeState = {
    pure: function (a) {
        return new State(function (s) {
            return new Tuple(s, a);
        });
    },
    Apply0: function () {
        return $lazy_applyState(0);
    }
};
var $lazy_functorState = /* #__PURE__ */ $runtime_lazy("functorState", "Main", function () {
    return {
        map: Control_Monad.liftM1(monadState)
    };
});
var $lazy_applyState = /* #__PURE__ */ $runtime_lazy("applyState", "Main", function () {
    return {
        apply: Control_Monad.ap(monadState),
        Functor0: function () {
            return $lazy_functorState(0);
        }
    };
});
var functorState = /* #__PURE__ */ $lazy_functorState(16);
var applyState = /* #__PURE__ */ $lazy_applyState(19);
var discard = /* #__PURE__ */ Control_Bind.discard(Control_Bind.discardUnit)(bindState);
var modify1 = /* #__PURE__ */ modify(monadState)(monadStateState);
var bind = /* #__PURE__ */ Control_Bind.bind(bindState);
var pure = /* #__PURE__ */ Control_Applicative.pure(applicativeState);
var test = /* #__PURE__ */ runState("")(/* #__PURE__ */ discard(/* #__PURE__ */ modify1(/* #__PURE__ */ append("World!")))(function () {
    return discard(modify1(append("Hello, ")))(function () {
        return bind(get1)(function (v) {
            return pure(v);
        });
    });
}));
var main = /* #__PURE__ */ (function () {
    var t4 = test4(new Tuple(1, 0));
    var t3 = test3(1);
    var t2 = test2(Control_Category.identity(Control_Category.categoryFn));
    return Effect_Console.log("Done");
})();
export {
    get,
    put,
    Tuple,
    State,
    runState,
    modify,
    test,
    test2,
    test3,
    test4,
    test5,
    main,
    functorState,
    applyState,
    applicativeState,
    bindState,
    monadState,
    monadStateState
};
