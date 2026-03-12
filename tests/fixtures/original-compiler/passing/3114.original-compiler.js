import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Tuple from "../Data.Tuple/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
import * as VendoredVariant from "../VendoredVariant/index.js";
var on = /* #__PURE__ */ VendoredVariant.on();
var on1 = /* #__PURE__ */ on({
    reflectSymbol: function () {
        return "bar";
    }
});
var show = /* #__PURE__ */ Data_Show.show(/* #__PURE__ */ Data_Tuple.showTuple(Data_Show.showString)(Data_Show.showInt));
var on2 = /* #__PURE__ */ on({
    reflectSymbol: function () {
        return "foo";
    }
});
var show1 = /* #__PURE__ */ Data_Show.show(/* #__PURE__ */ Data_Maybe.showMaybe(Data_Show.showInt));
var _foo = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var _bar = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var main = /* #__PURE__ */ (function () {
    var case2 = on1(_bar)(function (a) {
        return "bar: " + show(a);
    })(on2(_foo)(function (a) {
        return "foo: " + show1(a);
    })(VendoredVariant.case_));
    var case1 = on1(_bar)(function (a) {
        return "bar: " + show(a);
    })(on2(_foo)(function (a) {
        return "foo: " + show1(a);
    })(VendoredVariant.case_));
    return Effect_Console.log("Done");
})();
export {
    _foo,
    _bar,
    main
};
