import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var Id = function (x) {
    return x;
};
var pu = function (v) {
    return pure(Data_Unit.unit);
};
var sampleC = {
    pu: pu
};
var sampleIdC = {
    pu: pu
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    pu,
    sampleC,
    Id,
    sampleIdC,
    main
};
