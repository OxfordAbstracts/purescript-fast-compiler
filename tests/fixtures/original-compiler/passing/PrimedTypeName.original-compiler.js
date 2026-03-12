import * as Effect_Console from "../Effect.Console/index.js";
var TP = /* #__PURE__ */ (function () {
    function TP() {

    };
    TP.value = new TP();
    return TP;
})();
var T = /* #__PURE__ */ (function () {
    function T() {

    };
    T.value = new T();
    return T;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var eqT = {
    eq: function (v) {
        return function (v1) {
            return true;
        };
    }
};
export {
    main,
    eqT
};
