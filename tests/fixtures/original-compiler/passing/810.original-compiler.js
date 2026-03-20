import * as Effect_Console from "../Effect.Console/index.js";
var Nothing = /* #__PURE__ */ (function () {
    function Nothing() {

    };
    Nothing.value = new Nothing();
    return Nothing;
})();
var Just = /* #__PURE__ */ (function () {
    function Just(value0) {
        this.value0 = value0;
    };
    Just.create = function (value0) {
        return new Just(value0);
    };
    return Just;
})();
var test = function (m) {
    var o = (function () {
        if (m instanceof Nothing) {
            return {
                x: Nothing.value
            };
        };
        if (m instanceof Just) {
            return {
                x: new Just(m.value0)
            };
        };
        throw new Error("Failed pattern match at Main (line 11, column 9 - line 12, column 44): " + [ m.constructor.name ]);
    })();
    return o.x;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Nothing,
    Just,
    test,
    main
};
