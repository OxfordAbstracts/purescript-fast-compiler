import * as Control_Apply from "../Control.Apply/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var add = /* #__PURE__ */ Data_Semiring.add(Data_Semiring.semiringNumber);
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
var test8 = function (v) {
    return new Just(new Just(1.0));
};
var test6 = function (dictPartial) {
    return function (mx) {
        return function (v) {
            var f = function (v1) {
                if (v1 instanceof Just) {
                    return v1.value0;
                };
                throw new Error("Failed pattern match at Main (line 52, column 5 - line 52, column 32): " + [ v1.constructor.name ]);
            };
            return new Just(f(mx));
        };
    };
};
var test10 = function (v) {
    var g = function (x) {
        return f(x) / 2.0;
    };
    var f = function (x) {
        return g(x) * 3.0;
    };
    return new Just(f(10.0));
};
var test1 = function (v) {
    return new Just("abc");
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var functorMaybe = {
    map: function (v) {
        return function (v1) {
            if (v1 instanceof Nothing) {
                return Nothing.value;
            };
            if (v1 instanceof Just) {
                return new Just(v(v1.value0));
            };
            throw new Error("Failed pattern match at Main (line 8, column 1 - line 10, column 30): " + [ v.constructor.name, v1.constructor.name ]);
        };
    }
};
var map = /* #__PURE__ */ Data_Functor.map(functorMaybe);
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
var apply = /* #__PURE__ */ Control_Apply.apply(applyMaybe);
var bindMaybe = {
    bind: function (v) {
        return function (v1) {
            if (v instanceof Nothing) {
                return Nothing.value;
            };
            if (v instanceof Just) {
                return v1(v.value0);
            };
            throw new Error("Failed pattern match at Main (line 19, column 1 - line 21, column 24): " + [ v.constructor.name, v1.constructor.name ]);
        };
    },
    Apply0: function () {
        return applyMaybe;
    }
};
var bind = /* #__PURE__ */ Control_Bind.bind(bindMaybe);
var test2 = function (v) {
    return bind(new Just(1.0))(function (x) {
        return bind(new Just(2.0))(function (y) {
            return new Just(x + y);
        });
    });
};
var test3 = function (v) {
    return bind(new Just(1.0))(function () {
        return bind(Nothing.value)(function () {
            return new Just(2.0);
        });
    });
};
var test4 = function (mx) {
    return function (my) {
        return bind(mx)(function (x) {
            return bind(my)(function (y) {
                return new Just(x + y + 1.0);
            });
        });
    };
};
var test5 = function (mx) {
    return function (my) {
        return function (mz) {
            return bind(mx)(function (x) {
                return bind(my)(function (y) {
                    var sum = x + y;
                    return bind(mz)(function (z) {
                        return new Just(z + sum + 1.0);
                    });
                });
            });
        };
    };
};
var test9 = function (v) {
    return apply(map(add)(new Just(1.0)))(new Just(2.0));
};
var applicativeMaybe = /* #__PURE__ */ (function () {
    return {
        pure: Just.create,
        Apply0: function () {
            return applyMaybe;
        }
    };
})();
var monadMaybe = {
    Applicative0: function () {
        return applicativeMaybe;
    },
    Bind1: function () {
        return bindMaybe;
    }
};
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
    main,
    functorMaybe,
    applyMaybe,
    applicativeMaybe,
    bindMaybe,
    monadMaybe
};
