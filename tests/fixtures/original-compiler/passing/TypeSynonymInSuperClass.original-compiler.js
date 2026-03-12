import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var ask = function (dict) {
    return dict.ask;
};
var test = function (dictMonadAskEnv) {
    var MonadAsk1 = dictMonadAskEnv.MonadAsk1();
    var Monad0 = MonadAsk1.Monad0();
    var pure = Control_Applicative.pure(Monad0.Applicative0());
    return Control_Bind.bind(Monad0.Bind1())(ask(MonadAsk1))(function (v) {
        return pure(v.foo === "test");
    });
};
export {
    ask,
    test,
    main
};
