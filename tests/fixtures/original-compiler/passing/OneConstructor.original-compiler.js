import * as Effect_Console from "../Effect.Console/index.js";
var One = /* #__PURE__ */ (function () {
    function One(value0) {
        this.value0 = value0;
    };
    One.create = function (value0) {
        return new One(value0);
    };
    return One;
})();
var one$prime = function (v) {
    return v.value0;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    One,
    one$prime,
    main
};
