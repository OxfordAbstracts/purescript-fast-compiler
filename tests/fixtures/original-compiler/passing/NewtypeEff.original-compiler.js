import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Apply from "../Control.Apply/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Effect.functorEffect);
var apply = /* #__PURE__ */ Control_Apply.apply(Effect.applyEffect);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var T = function (x) {
    return x;
};
var runT = function (v) {
    return v;
};
var functorT = {
    map: function (f) {
        return function (v) {
            return map(f)(v);
        };
    }
};
var applyT = {
    apply: function (v) {
        return function (v1) {
            return apply(v)(v1);
        };
    },
    Functor0: function () {
        return functorT;
    }
};
var bindT = {
    bind: function (v) {
        return function (f) {
            return function __do() {
                var x = v();
                return runT(f(x))();
            };
        };
    },
    Apply0: function () {
        return applyT;
    }
};
var discard = /* #__PURE__ */ Control_Bind.discard(Control_Bind.discardUnit)(bindT);
var main = /* #__PURE__ */ runT(/* #__PURE__ */ discard(/* #__PURE__ */ Effect_Console.log("Done"))(function () {
    return discard(Effect_Console.log("Done"))(function () {
        return Effect_Console.log("Done");
    });
}));
var applicativeT = {
    pure: function (t) {
        return pure(t);
    },
    Apply0: function () {
        return applyT;
    }
};
var monadT = {
    Applicative0: function () {
        return applicativeT;
    },
    Bind1: function () {
        return bindT;
    }
};
export {
    T,
    runT,
    main,
    functorT,
    applyT,
    applicativeT,
    bindT,
    monadT
};
