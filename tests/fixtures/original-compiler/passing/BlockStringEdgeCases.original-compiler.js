import * as Data_Eq from "../Data.Eq/index.js";
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
var tupleEq = function (dictEq) {
    var eq2 = Data_Eq.eq(dictEq);
    return function (dictEq1) {
        var eq3 = Data_Eq.eq(dictEq1);
        return {
            eq: function (x) {
                return function (y) {
                    return eq2(x.value0)(y.value0) && eq3(x.value1)(y.value1);
                };
            }
        };
    };
};
var eq1 = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ tupleEq(Data_Eq.eqString)(Data_Eq.eqString));
var main = function __do() {
    Test_Assert["assert$prime"]("empty string")("" === "")();
    Test_Assert["assert$prime"]("quote")("\"" === "\"")();
    Test_Assert["assert$prime"]("starts with quote")("\"x" === "\"x")();
    Test_Assert["assert$prime"]("ends with quote")("x\"" === "x\"")();
    Test_Assert["assert$prime"]("two quotes")("\"\"" === "\"\"")();
    Test_Assert["assert$prime"]("starts with two quotes")("\"\"x" === "\"\"x")();
    Test_Assert["assert$prime"]("ends with two quotes")("x\"\"" === "x\"\"")();
    Test_Assert["assert$prime"]("starts and ends with two quotes")("\"\"x\"\"" === "\"\"x\"\"")();
    Test_Assert["assert$prime"]("mixture 1")("\"\"x\"y\"\"z\"" === "\"\"x\"y\"\"z\"")();
    Test_Assert["assert$prime"]("mixture 2")("x\"y\"\"z" === "x\"y\"\"z")();
    Test_Assert["assert$prime"]("too many quotes 1")(eq1(new Tuple("\"\"", " "))(new Tuple("\"\"", " ")))();
    Test_Assert["assert$prime"]("too many quotes 2")(eq1(new Tuple("\"\"", ""))(new Tuple("\"\"", "")))();
    Test_Assert["assert$prime"]("too many quotes 3")(eq1(new Tuple("x\"\"", " "))(new Tuple("x\"\"", " ")))();
    Test_Assert["assert$prime"]("too many quotes 4")(eq1(new Tuple("x\"\"", ""))(new Tuple("x\"\"", "")))();
    return Effect_Console.log("Done")();
};
export {
    Tuple,
    main,
    tupleEq
};
