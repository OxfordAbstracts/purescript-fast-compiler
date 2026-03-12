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
var test2 = /* #__PURE__ */ (function () {
    return Nothing.value;
})();
var test1 = /* #__PURE__ */ (function () {
    return new Just(10);
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Nothing,
    Just,
    test1,
    test2,
    main
};
