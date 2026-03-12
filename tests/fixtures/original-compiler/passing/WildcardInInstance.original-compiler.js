import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Control_Monad from "../Control.Monad/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var monadAskFun = {
    ask: /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn),
    Monad0: function () {
        return Control_Monad.monadFn;
    }
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var ask = function (dict) {
    return dict.ask;
};
var test = function (dictMonadAsk) {
    var Monad0 = dictMonadAsk.Monad0();
    var pure = Control_Applicative.pure(Monad0.Applicative0());
    return Control_Bind.bind(Monad0.Bind1())(ask(dictMonadAsk))(function (x) {
        return pure(x + 1 | 0);
    });
};
export {
    ask,
    test,
    main,
    monadAskFun
};
