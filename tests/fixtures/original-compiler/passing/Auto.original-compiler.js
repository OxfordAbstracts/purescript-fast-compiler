import * as Effect_Console from "../Effect.Console/index.js";
var Auto = /* #__PURE__ */ (function () {
    function Auto(value0) {
        this.value0 = value0;
    };
    Auto.create = function (value0) {
        return new Auto(value0);
    };
    return Auto;
})();
var run = function (s) {
    return function (i) {
        return s(function (a) {
            return a.value0.step(a.value0.state)(i);
        });
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var exists = function (state) {
    return function (step) {
        return function (f) {
            return f(new Auto({
                state: state,
                step: step
            }));
        };
    };
};
export {
    Auto,
    exists,
    run,
    main
};
