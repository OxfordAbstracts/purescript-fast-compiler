import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var replicateM_ = function (dictMonad) {
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    var bind = Control_Bind.bind(dictMonad.Bind1());
    return function (v) {
        return function (v1) {
            if (v === 0.0) {
                return pure(Data_Unit.unit);
            };
            return bind(v1)(function () {
                return replicateM_(dictMonad)(v - 1.0)(v1);
            });
        };
    };
};
var main = function __do() {
    replicateM_(Effect.monadEffect)(10.0)(Effect_Console.log("Hello World!"))();
    return Effect_Console.log("Done")();
};
export {
    replicateM_,
    main
};
