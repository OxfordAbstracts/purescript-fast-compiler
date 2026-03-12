import * as Effect_Console from "../Effect.Console/index.js";
var Empty = /* #__PURE__ */ (function () {
    function Empty() {

    };
    Empty.value = new Empty();
    return Empty;
})();
var Cons = /* #__PURE__ */ (function () {
    function Cons() {

    };
    Cons.value = new Cons();
    return Cons;
})();
var transitive = {
    d: function (v) {
        return {};
    }
};
var simple1 = {
    c: function (cons) {
        return {
            foo: cons
        };
    }
};
var simple0 = {
    c: function (v) {
        return {};
    }
};
var multipleDeterminers = {};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var determinedCycle = {};
var d = function (dict) {
    return dict.d;
};
var cyclic = {};
var c = function (dict) {
    return dict.c;
};
export {
    c,
    d,
    Empty,
    Cons,
    main,
    simple0,
    simple1,
    transitive,
    cyclic,
    determinedCycle,
    multipleDeterminers
};
