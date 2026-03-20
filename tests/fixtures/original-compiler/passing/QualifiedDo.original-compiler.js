import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as IxMonad from "../IxMonad/index.js";
var testMonad = function (dictMonad) {
    var bind = Control_Bind.bind(dictMonad.Bind1());
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return bind(pure("test"))(function (a) {
        return bind(pure("test"))(function (b) {
            return pure(a + b);
        });
    });
};
var testIMonad = function (dictIxMonad) {
    var bind = IxMonad.bind(dictIxMonad);
    var pure = IxMonad.pure(dictIxMonad);
    return bind(pure("test"))(function (a) {
        return bind(pure("test"))(function (b) {
            return pure(a + b);
        });
    });
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    testIMonad,
    testMonad,
    main
};
