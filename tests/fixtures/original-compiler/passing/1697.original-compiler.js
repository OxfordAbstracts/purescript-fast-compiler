import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var y = function (dictMonad) {
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return Control_Bind.bind(dictMonad.Bind1())(pure(Data_Unit.unit))(function () {
        return pure(Data_Unit.unit);
    });
};
var x = function (dictMonad) {
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return Control_Bind.bind(dictMonad.Bind1())(pure(Data_Unit.unit))(function () {
        return pure(Data_Unit.unit);
    });
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var _2 = function (a) {
    return a;
};
var wtf = function (dictMonad) {
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return Control_Bind.bind(dictMonad.Bind1())(pure(Data_Unit.unit))(function () {
        var tmp = _2(1);
        return pure(Data_Unit.unit);
    });
};
export {
    _2,
    x,
    y,
    wtf,
    main
};
