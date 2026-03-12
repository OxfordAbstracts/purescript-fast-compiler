import * as Effect_Console from "../Effect.Console/index.js";
var I = /* #__PURE__ */ (function () {
    function I(value0) {
        this.value0 = value0;
    };
    I.create = function (value0) {
        return new I(value0);
    };
    return I;
})();
var defaultString = {
    def: "Done"
};
var def = function (dict) {
    return dict.def;
};
var defaultI = function (dictDefault) {
    return {
        def: new I(def(dictDefault))
    };
};
var main = /* #__PURE__ */ (function () {
    var v = def(defaultI(defaultString));
    return Effect_Console.log(v.value0);
})();
export {
    def,
    I,
    main,
    defaultString,
    defaultI
};
