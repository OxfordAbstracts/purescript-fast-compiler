import * as Control_Monad_ST_Internal from "../Control.Monad.ST.Internal/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Control_Monad_ST_Internal.functorST);
var greaterThan = /* #__PURE__ */ Data_Ord.greaterThan(Data_Ord.ordNumber);
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fib = /* #__PURE__ */ (function __do() {
    var n1 = {
        value: 1.0
    };
    var n2 = {
        value: 1.0
    };
    (function () {
        while (map(greaterThan(1000.0))(Control_Monad_ST_Internal.read(n1))()) {
            (function __do() {
                var n1$prime = n1.value;
                var n2$prime = n2.value;
                n2.value = n1$prime + n2$prime;
                return n1.value = n2$prime;
            })();
        };
        return {};
    })();
    return n2.value;
})();
export {
    fib,
    main
};
