import * as Effect_Console from "../Effect.Console/index.js";
var Cons = /* #__PURE__ */ (function () {
    function Cons(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Cons.create = function (value0) {
        return function (value1) {
            return new Cons(value0, value1);
        };
    };
    return Cons;
})();
var step = function (v) {
    return v.value1;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var head = function (xs) {
    var $5 = step(xs);
    return $5.value0;
};
export {
    Cons,
    step,
    head,
    main
};
