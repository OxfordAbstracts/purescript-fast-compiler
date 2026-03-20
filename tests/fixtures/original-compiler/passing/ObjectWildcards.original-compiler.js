import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var map = /* #__PURE__ */ Data_Functor.map(Effect.functorEffect);
var logShow = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showBoolean);
var mkRecord = function (v) {
    return function (v1) {
        return {
            foo: v,
            bar: v1,
            baz: "baz"
        };
    };
};
var getValue = /* #__PURE__ */ pure(true);
var main = function __do() {
    var obj = map(function (v) {
        return {
            value: v
        };
    })(getValue)();
    logShow(obj.value)();
    var point = map(function (v) {
        return {
            x: v,
            y: 1.0
        };
    })(pure(2.0))();
    Test_Assert.assert(point.x === 2.0)();
    Test_Assert.assert(point.y === 1.0)();
    return Effect_Console.log((mkRecord(1.0)("Done")).bar)();
};
export {
    mkRecord,
    getValue,
    main
};
