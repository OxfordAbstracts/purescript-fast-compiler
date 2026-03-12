import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var X = /* #__PURE__ */ (function () {
    function X() {

    };
    X.value = new X();
    return X;
})();
var Y = /* #__PURE__ */ (function () {
    function Y() {

    };
    Y.value = new Y();
    return Y;
})();
var show = 1.0;
var noshow = function (dict) {
    return dict.noshow;
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showNumber)(show)();
    return Effect_Console.log("Done")();
};
export {
    noshow,
    show,
    X,
    Y,
    main
};
