import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showString);
var test = function (dictShow) {
    var show1 = Data_Show.show(dictShow);
    return function (str) {
        return function (num) {
            var $9 = show1(num) === str;
            if ($9) {
                return pure(Data_Unit.unit);
            };
            return Data_Function.flip(Test_Assert["assert$prime"])(false)("Expected " + (show(str) + (", got " + (show(show1(num)) + "."))));
        };
    };
};
var test1 = /* #__PURE__ */ test(Data_Show.showNumber);
var main = function __do() {
    test1("0.17")(0.17)();
    test1("0.25996181067141905")(0.25996181067141905)();
    test1("0.3572019862807257")(0.3572019862807257)();
    test1("0.46817723004874223")(0.46817723004874223)();
    test1("0.9640035681058178")(0.9640035681058178)();
    test1("4.23808622486133")(4.23808622486133)();
    test1("4.540362294799751")(4.540362294799751)();
    test1("5.212384849884261")(5.212384849884261)();
    test1("13.958257048123212")(13.958257048123212)();
    test1("32.96176575630599")(32.96176575630599)();
    test1("38.47735512322269")(38.47735512322269)();
    test1("10000000000.0")(1.0e10)();
    test1("10000000000.0")(1.0e10)();
    test1("0.00001")(1.0e-5)();
    test1("0.00001")(1.0e-5)();
    test1("1.5339794352098402e-118")(1.5339794352098402e-118)();
    test1("2.108934760892056e-59")(2.108934760892056e-59)();
    test1("2.250634744599241e-19")(2.250634744599241e-19)();
    test1("5.960464477539063e-8")(5.960464477539063e-8)();
    test1("5e-324")(5.0e-324)();
    test1("5e-324")(5.0e-324)();
    return Effect_Console.log("Done")();
};
export {
    main,
    test
};
