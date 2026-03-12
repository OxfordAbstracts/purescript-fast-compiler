import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showString);
var Thing = function (x) {
    return x;
};
var Box = function (x) {
    return x;
};
var showThing = {
    show: function (v) {
        return "Thing " + show(v);
    }
};
var showBox = function (dictShow) {
    var show1 = Data_Show.show(dictShow);
    return {
        show: function (v) {
            return "Box " + show1(v);
        }
    };
};
var logShow = /* #__PURE__ */ Effect_Console.logShow(/* #__PURE__ */ showBox(Data_Show.showNumber));
var apply = function (f) {
    return function (x) {
        return f(x);
    };
};
var main = function __do() {
    Effect_Console.logShow(showThing)("hello")();
    logShow(42.0)();
    logShow(apply(Box)(9000.0))();
    return Effect_Console.log("Done")();
};
export {
    Thing,
    Box,
    apply,
    main,
    showThing,
    showBox
};
