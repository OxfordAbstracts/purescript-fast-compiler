import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var suNumber = {
    su: function (n) {
        return n + 1.0;
    }
};
var su = function (dict) {
    return dict.su;
};
var clNumber = {
    cl: function (n) {
        return function (m) {
            return n + m;
        };
    },
    Su0: function () {
        return suNumber;
    }
};
var cl = function (dict) {
    return dict.cl;
};
var test = function (dictCl) {
    var su1 = su(dictCl.Su0());
    var cl1 = cl(dictCl);
    return function (a) {
        return su1(cl1(a)(a));
    };
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showNumber)(test(clNumber)(10.0))();
    return Effect_Console.log("Done")();
};
export {
    cl,
    su,
    test,
    main,
    suNumber,
    clNumber
};
