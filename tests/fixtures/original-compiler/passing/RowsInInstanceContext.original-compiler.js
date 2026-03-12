import * as Control_Category from "../Control.Category/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var RecordNewtype = function (x) {
    return x;
};
var wrap = function (dict) {
    return dict.wrap;
};
var unwrap = function (dict) {
    return dict.unwrap;
};
var refl = {
    coerce: identity,
    coerceBack: identity
};
var coerceBack = function (dict) {
    return dict.coerceBack;
};
var coerce = function (dict) {
    return dict.coerce;
};
var newtypeRecordNewtype = function (dictTypeEquals) {
    var coerceBack1 = coerceBack(dictTypeEquals);
    return {
        wrap: (function () {
            var $13 = coerce(dictTypeEquals);
            return function ($14) {
                return RecordNewtype($13($14));
            };
        })(),
        unwrap: function (v) {
            return coerceBack1(v);
        }
    };
};
var main = /* #__PURE__ */ (function () {
    return Effect_Console.log((unwrap(newtypeRecordNewtype(refl))({
        x: "Done"
    })).x);
})();
export {
    coerce,
    coerceBack,
    unwrap,
    wrap,
    RecordNewtype,
    main,
    refl,
    newtypeRecordNewtype
};
