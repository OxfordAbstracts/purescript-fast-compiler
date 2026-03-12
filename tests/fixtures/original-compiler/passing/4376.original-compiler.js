import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var v1 = /* #__PURE__ */ (function () {
    return {
        a: new Data_Maybe.Just(Data_Unit.unit)
    };
})();
var v2 = /* #__PURE__ */ (function () {
    var v3 = {
        a: Data_Monoid.mempty(Data_Maybe.monoidMaybe(Data_Semigroup.semigroupUnit))
    };
    return v3;
})();
var union = function () {
    return function (v) {
        return function (v3) {
            return Type_Proxy["Proxy"].value;
        };
    };
};
var shouldSolve = /* #__PURE__ */ (function () {
    return union()({
        a: Data_Maybe.Nothing.value
    })({
        b: Data_Maybe.Nothing.value
    });
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var asNothing = function (v) {
    return {
        a: Data_Maybe.Nothing.value
    };
};
export {
    asNothing,
    union,
    shouldSolve,
    v1,
    v2,
    main
};
