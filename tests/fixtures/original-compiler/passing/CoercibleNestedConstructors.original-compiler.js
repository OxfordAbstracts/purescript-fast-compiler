import * as Effect_Console from "../Effect.Console/index.js";
import * as Safe_Coerce from "../Safe.Coerce/index.js";
var coerce = /* #__PURE__ */ Safe_Coerce.coerce();
var Pair = /* #__PURE__ */ (function () {
    function Pair(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Pair.create = function (value0) {
        return function (value1) {
            return new Pair(value0, value1);
        };
    };
    return Pair;
})();
var N = function (x) {
    return x;
};
var Id = function (x) {
    return x;
};
var unwrapPair = coerce;
var main = /* #__PURE__ */ Effect_Console.log("Done");
var convert = function (x) {
    var result = coerce(x);
    return result;
};
export {
    Id,
    N,
    Pair,
    unwrapPair,
    convert,
    main
};
