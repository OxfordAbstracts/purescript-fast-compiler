import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var zero$prime = function (z) {
    return function (v) {
        return z;
    };
};
var succ = function (f) {
    return function (zero$prime1) {
        return function (succ1) {
            return succ1(f(zero$prime1)(succ1));
        };
    };
};
var runNat = function (f) {
    return f(0.0)(function (n) {
        return n + 1.0;
    });
};
var one$prime = /* #__PURE__ */ succ(zero$prime);
var two = /* #__PURE__ */ succ(one$prime);
var add = function (f) {
    return function (g) {
        return function (zero$prime1) {
            return function (succ1) {
                return g(f(zero$prime1)(succ1))(succ1);
            };
        };
    };
};
var four = /* #__PURE__ */ add(two)(two);
var fourNumber = /* #__PURE__ */ runNat(four);
var main = function __do() {
    Effect_Console.log(Data_Show.show(Data_Show.showNumber)(fourNumber))();
    return Effect_Console.log("Done")();
};
export {
    runNat,
    zero$prime,
    succ,
    add,
    one$prime,
    two,
    four,
    fourNumber,
    main
};
