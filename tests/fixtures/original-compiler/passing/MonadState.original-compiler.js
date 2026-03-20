import * as Control_Bind from "../Control.Bind/index.js";
import * as Control_Monad from "../Control.Monad/index.js";
import * as Data_Show from "../Data.Show/index.js";
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
var showTuple = function (dictShow) {
    var show = Data_Show.show(dictShow);
    return function (dictShow1) {
        var show1 = Data_Show.show(dictShow1);
        return {
            show: function (v) {
                return "(" + (show(v.value0) + (", " + (show1(v.value1) + ")")));
            }
        };
    };
};
var runState = function (s) {
    return function (v) {
        return v.value0(s);
    };
};
var put = function (dict) {
    return dict.put;
};
var get = function (dict) {
    return dict.get;
};
var modify = function (dictBind) {
    var bind = Control_Bind.bind(dictBind);
    return function (dictMonadState) {
        var get1 = get(dictMonadState);
        var put1 = put(dictMonadState);
        return function (f) {
            return bind(get1)(function (s) {
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
var functorState = /* #__PURE__ */ $lazy_functorState(19);
var applyState = /* #__PURE__ */ $lazy_applyState(22);
var monadStateState = /* #__PURE__ */ (function () {
    return {
        get: new State(function (s) {
            return new Tuple(s, s);
        }),
        put: function (s) {
            return new State(function (v) {
                return new Tuple(s, Data_Unit.unit);
            });
        },
        Monad0: function () {
            return monadState;
        }
    };
})();
var main = function __do() {
    Effect_Console.logShow(showTuple(Data_Show.showInt)(Data_Show.showUnit))(runState(0)(modify(bindState)(monadStateState)(function (v) {
        return v + 1 | 0;
    })))();
    return Effect_Console.log("Done")();
};
export {
    get,
    put,
    Tuple,
    State,
    runState,
    modify,
    main,
    showTuple,
    functorState,
    applyState,
    applicativeState,
    bindState,
    monadState,
    monadStateState
};
