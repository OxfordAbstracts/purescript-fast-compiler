import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var B = /* #__PURE__ */ (function () {
    function B(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    B.create = function (value0) {
        return function (value1) {
            return new B(value0, value1);
        };
    };
    return B;
})();
var memptyB = function (dictMonoid) {
    var mempty = Data_Monoid.mempty(dictMonoid);
    var r = function (v) {
        return mempty;
    };
    var l = function (v) {
        return mempty;
    };
    return new B(l, r);
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showBoolean)((function () {
        var v = memptyB(Data_Monoid.monoidArray);
        return Data_Eq.eq(Data_Eq.eqArray(Data_Eq.eqUnit))(v.value0(0))(v.value1(0));
    })())();
    return Effect_Console.log("Done")();
};
export {
    B,
    memptyB,
    main
};
