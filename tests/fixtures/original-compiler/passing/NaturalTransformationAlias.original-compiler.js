import * as Effect_Console from "../Effect.Console/index.js";
var Box = /* #__PURE__ */ (function () {
    function Box(value0) {
        this.value0 = value0;
    };
    Box.create = function (value0) {
        return new Box(value0);
    };
    return Box;
})();
var unbox = function (v) {
    return v.value0;
};
var mapBox = function (nat) {
    return function (v) {
        return new Box(nat(v.value0));
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Box,
    unbox,
    mapBox,
    main
};
