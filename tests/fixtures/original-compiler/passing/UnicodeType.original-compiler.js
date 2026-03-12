import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var f2 = function (dict) {
    return dict.f2;
};
var f1 = function (dict) {
    return dict.f1;
};
var f$prime = function (dictMonad) {
    var bind = Control_Bind.bind(dictMonad.Bind1());
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return function (n) {
        return bind(pure(n))(function (n$prime) {
            return pure(n$prime);
        });
    };
};
var f = function (dictMonad) {
    var bind = Control_Bind.bind(dictMonad.Bind1());
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return function (n) {
        return bind(pure(n))(function (n$prime) {
            return pure(n$prime);
        });
    };
};
export {
    f1,
    f2,
    f,
    f$prime,
    main
};
