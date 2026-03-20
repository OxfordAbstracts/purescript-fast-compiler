import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var Tuple = /* #__PURE__ */ (function () {
    function Tuple(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Tuple.create = function (value0) {
        return function (value1) {
            return new Tuple(value0, value1);
        };
    };
    return Tuple;
})();
var test5 = /* #__PURE__ */ (function () {
    var v = new Tuple(-7 | 0, 8);
    if (v.value0 === -7) {
        return v.value1;
    };
    return 0;
})();
var test4 = /* #__PURE__ */ (function () {
    var v = new Tuple(7, -3 | 0);
    if (v.value1 === -3) {
        return v.value0;
    };
    return 0;
})();
var test3 = function (v) {
    return v.value0.value0;
};
var test2 = /* #__PURE__ */ (function () {
    var v = new Tuple(3, 4);
    if (v.value1 === 4) {
        return v.value0;
    };
    return 0;
})();
var test1 = /* #__PURE__ */ (function () {
    var tuple = new Tuple("", "");
    return tuple.value0;
})();
var main = function __do() {
    Test_Assert.assert(test1 === "")();
    Test_Assert.assert(test2 === 3)();
    Test_Assert.assert(test3(new Tuple(new Tuple(5, 10), 15)) === 5)();
    Test_Assert.assert(test4 === 7)();
    Test_Assert.assert(test5 === 8)();
    return Effect_Console.log("Done")();
};
export {
    Tuple,
    test1,
    test2,
    test3,
    test4,
    test5,
    main
};
