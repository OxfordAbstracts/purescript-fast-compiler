import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var logShow = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showNumber);
var foo = function (x) {
    return function (dictMonad) {
        return Control_Applicative.pure(dictMonad.Applicative0())(x);
    };
};
var bar = function (dictMonad) {
    return foo(3.0)(dictMonad);
};
var main = function __do() {
    var x = bar(Effect.monadEffect)();
    logShow(x)();
    return Effect_Console.log("Done")();
};
export {
    foo,
    bar,
    main
};
