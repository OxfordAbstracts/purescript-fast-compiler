import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Control_Monad from "../Control.Monad/index.js";
import * as Data_Show from "../Data.Show/index.js";
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
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showString);
var bind = /* #__PURE__ */ Control_Bind.bind(Control_Bind.bindFn);
var pure = /* #__PURE__ */ Control_Applicative.pure(Control_Applicative.applicativeFn);
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
var Data = /* #__PURE__ */ (function () {
    function Data(value0) {
        this.value0 = value0;
    };
    Data.create = function (value0) {
        return new Data(value0);
    };
    return Data;
})();
var test8 = function (v) {
    return show("testing");
};
var test7 = function (dictShow) {
    return Data_Show.show(dictShow);
};
var test4 = function (dictMonad) {
    var pure2 = Control_Applicative.pure(dictMonad.Applicative0());
    return function (v) {
        return pure2(1.0);
    };
};
var test1 = function (v) {
    return show("testing");
};
var showData = function (dictShow) {
    var show2 = Data_Show.show(dictShow);
    return {
        show: function (v) {
            return "Data (" + (show2(v.value0) + ")");
        }
    };
};
var show1 = /* #__PURE__ */ Data_Show.show(/* #__PURE__ */ showData(Data_Show.showString));
var test3 = function (v) {
    return show1(new Data("testing"));
};
var runReader = function (r) {
    return function (f2) {
        return f2(r);
    };
};
var main = function __do() {
    Effect_Console.log(test7(Data_Show.showString)("Hello"))();
    return Effect_Console.log("Done")();
};
var f = function (dictShow) {
    var show2 = Data_Show.show(dictShow);
    return function (x) {
        return show2(x);
    };
};
var f1 = /* #__PURE__ */ f(Data_Show.showString);
var test2 = function (v) {
    return f1("testing");
};
var ask = function (r) {
    return r;
};
var test9 = function (v) {
    return runReader(0.0)(bind(ask)(function (n) {
        return pure(n + 1.0);
    }));
};
var monadMaybe = {
    Applicative0: function () {
        return applicativeMaybe;
    },
    Bind1: function () {
        return bindMaybe;
    }
};
var bindMaybe = {
    bind: function (v) {
        return function (v1) {
            if (v instanceof Nothing) {
                return Nothing.value;
            };
            if (v instanceof Just) {
                return v1(v.value0);
            };
            throw new Error("Failed pattern match at Main (line 50, column 1 - line 52, column 24): " + [ v.constructor.name, v1.constructor.name ]);
        };
    },
    Apply0: function () {
        return $lazy_applyMaybe(0);
    }
};
var applicativeMaybe = /* #__PURE__ */ (function () {
    return {
        pure: Just.create,
        Apply0: function () {
            return $lazy_applyMaybe(0);
        }
    };
})();
var $lazy_functorMaybe = /* #__PURE__ */ $runtime_lazy("functorMaybe", "Main", function () {
    return {
        map: Control_Monad.liftM1(monadMaybe)
    };
});
var $lazy_applyMaybe = /* #__PURE__ */ $runtime_lazy("applyMaybe", "Main", function () {
    return {
        apply: Control_Monad.ap(monadMaybe),
        Functor0: function () {
            return $lazy_functorMaybe(0);
        }
    };
});
var functorMaybe = /* #__PURE__ */ $lazy_functorMaybe(41);
var applyMaybe = /* #__PURE__ */ $lazy_applyMaybe(44);
var bind1 = /* #__PURE__ */ Control_Bind.bind(bindMaybe);
var pure1 = /* #__PURE__ */ Control_Applicative.pure(applicativeMaybe);
var test5 = function (v) {
    return bind1(new Just(1.0))(function (n) {
        return pure1(n + 1.0);
    });
};
var monadData = {
    Applicative0: function () {
        return applicativeData;
    },
    Bind1: function () {
        return bindData;
    }
};
var bindData = {
    bind: function (v) {
        return function (f2) {
            return f2(v.value0);
        };
    },
    Apply0: function () {
        return $lazy_applyData(0);
    }
};
var applicativeData = /* #__PURE__ */ (function () {
    return {
        pure: Data.create,
        Apply0: function () {
            return $lazy_applyData(0);
        }
    };
})();
var $lazy_functorData = /* #__PURE__ */ $runtime_lazy("functorData", "Main", function () {
    return {
        map: Control_Monad.liftM1(monadData)
    };
});
var $lazy_applyData = /* #__PURE__ */ $runtime_lazy("applyData", "Main", function () {
    return {
        apply: Control_Monad.ap(monadData),
        Functor0: function () {
            return $lazy_functorData(0);
        }
    };
});
var functorData = /* #__PURE__ */ $lazy_functorData(25);
var applyData = /* #__PURE__ */ $lazy_applyData(28);
export {
    test1,
    f,
    test2,
    test7,
    test8,
    Data,
    test3,
    Nothing,
    Just,
    test4,
    test5,
    ask,
    runReader,
    test9,
    main,
    showData,
    functorData,
    applyData,
    applicativeData,
    bindData,
    monadData,
    functorMaybe,
    applyMaybe,
    applicativeMaybe,
    bindMaybe,
    monadMaybe
};
