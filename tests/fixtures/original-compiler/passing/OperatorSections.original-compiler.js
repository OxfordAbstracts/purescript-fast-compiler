import * as Data_Function from "../Data.Function/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var main = function __do() {
    Test_Assert.assert((function (v) {
        return v / 2.0;
    })(4.0) === 2.0)();
    Test_Assert.assert((function (v) {
        return 2.0 / v;
    })(4.0) === 0.5)();
    Test_Assert.assert((function (v) {
        return Data_Function["const"](v)(1.0);
    })(2.0) === 2.0)();
    Test_Assert.assert((function (v) {
        return Data_Function["const"](1.0)(v);
    })(2.0) === 1.0)();
    var foo = {
        x: 2.0
    };
    Test_Assert.assert((function (v) {
        return v / foo.x;
    })(4.0) === 2.0)();
    Test_Assert.assert((function (v) {
        return foo.x / v;
    })(4.0) === 0.5)();
    var div1 = function (x) {
        return function (y) {
            return x.x / y.x;
        };
    };
    Test_Assert.assert((function (v) {
        return div1(v)({
            x: 4.0
        });
    })({
        x: 4.0
    }) === 1.0)();
    Test_Assert.assert((function (v) {
        return div1({
            x: 4.0
        })(v);
    })({
        x: 4.0
    }) === 1.0)();
    Test_Assert.assert((function (v) {
        return v + (2 * 3 | 0) | 0;
    })(1) === 7)();
    Test_Assert.assert((function (v) {
        return (3 * 2 | 0) + v | 0;
    })(1) === 7)();
    return Effect_Console.log("Done")();
};
export {
    main
};
