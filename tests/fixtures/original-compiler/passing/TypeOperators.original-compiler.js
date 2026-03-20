import * as A from "../A/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var UseOperatorInDataParamKind = /* #__PURE__ */ (function () {
    function UseOperatorInDataParamKind() {

    };
    UseOperatorInDataParamKind.value = new UseOperatorInDataParamKind();
    return UseOperatorInDataParamKind;
})();
var Compose = /* #__PURE__ */ (function () {
    function Compose(value0) {
        this.value0 = value0;
    };
    Compose.create = function (value0) {
        return new Compose(value0);
    };
    return Compose;
})();
var testPrecedence2 = function (nat) {
    return function (fx) {
        return nat(fx);
    };
};
var testPrecedence1 = function (x) {
    return x;
};
var testParens = function (nat) {
    return nat;
};
var swap = function (v) {
    return new A.Tuple(v.value1, v.value0);
};
var natty = function (x) {
    return x;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    natty,
    Compose,
    testPrecedence1,
    testPrecedence2,
    testParens,
    swap,
    UseOperatorInDataParamKind,
    main
};
