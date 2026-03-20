import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var getValue = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect)(true);
var main = /* #__PURE__ */ (function () {
    var record = {
        value: false
    };
    return function __do() {
        var record$prime = Data_Functor.map(Effect.functorEffect)(function (v) {
            return {
                value: v
            };
        })(getValue)();
        Test_Assert.assert(record$prime.value === true)();
        var point = {
            x: 1.0,
            y: 1.0
        };
        var point$prime = (function (v) {
            return {
                x: v,
                y: 10.0
            };
        })(100.0);
        Test_Assert.assert(point$prime.x === 100.0)();
        Test_Assert.assert(point$prime.y === 10.0)();
        var record2 = (function (v) {
            return function (v1) {
                return {
                    x: v1
                };
            };
        })({
            x: 0.0
        })(10.0);
        Test_Assert.assert(record2.x === 10.0)();
        return Effect_Console.log("Done")();
    };
})();
export {
    getValue,
    main
};
