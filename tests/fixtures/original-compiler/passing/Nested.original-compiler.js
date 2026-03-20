import * as Effect_Console from "../Effect.Console/index.js";
var Extend = /* #__PURE__ */ (function () {
    function Extend(value0) {
        this.value0 = value0;
    };
    Extend.create = function (value0) {
        return new Extend(value0);
    };
    return Extend;
})();
var Square = /* #__PURE__ */ (function () {
    function Square(value0) {
        this.value0 = value0;
    };
    Square.create = function (value0) {
        return new Square(value0);
    };
    return Square;
})();
var Bigger = /* #__PURE__ */ (function () {
    function Bigger(value0) {
        this.value0 = value0;
    };
    Bigger.create = function (value0) {
        return new Bigger(value0);
    };
    return Bigger;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Extend,
    Square,
    Bigger,
    main
};
