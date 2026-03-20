import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Tuple from "../Data.Tuple/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var singleArgument = function (v) {
    return Data_Unit.unit;
};
var singleApplication = singleArgument;
var otherNestingWorks = /* #__PURE__ */ (function () {
    return [ new Data_Maybe.Just(new Data_Tuple.Tuple(0, 0.0)), new Data_Maybe.Just(new Data_Tuple.Tuple(1, 1.0)) ];
})();
var operatorAsArgument = /* #__PURE__ */ (function () {
    return Type_Proxy["Proxy"].value;
})();
var multiArgument = function (v) {
    return function (v1) {
        return Data_Unit.unit;
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var inSynonym = singleArgument;
var appNestingWorks = multiArgument;
export {
    singleArgument,
    multiArgument,
    singleApplication,
    appNestingWorks,
    otherNestingWorks,
    inSynonym,
    operatorAsArgument,
    main
};
