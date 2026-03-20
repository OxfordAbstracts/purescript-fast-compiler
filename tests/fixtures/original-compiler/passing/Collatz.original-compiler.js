import * as Control_Monad_ST_Internal from "../Control.Monad.ST.Internal/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Control_Monad_ST_Internal.functorST);
var $$void = /* #__PURE__ */ Data_Functor["void"](Control_Monad_ST_Internal.functorST);
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt);
var div = /* #__PURE__ */ Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt);
var collatz = function (n) {
    return (function __do() {
        var r = {
            value: n
        };
        var count = {
            value: 0
        };
        (function () {
            while (map(function (v) {
                return v !== 1;
            })(Control_Monad_ST_Internal.read(r))()) {
                (function __do() {
                    count.value = (function (v) {
                        return v + 1 | 0;
                    })(count.value);
                    return $$void(Control_Monad_ST_Internal.write((function () {
                        var $15 = mod(r.value)(2) === 0;
                        if ($15) {
                            return div(r.value)(2);
                        };
                        return (3 * r.value | 0) + 1 | 0;
                    })())(r))();
                })();
            };
            return {};
        })();
        return count.value;
    })();
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showInt)(collatz(1000))();
    return Effect_Console.log("Done")();
};
export {
    collatz,
    main
};
