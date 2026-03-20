import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var Identity = /* #__PURE__ */ (function () {
    function Identity(value0) {
        this.value0 = value0;
    };
    Identity.create = function (value0) {
        return new Identity(value0);
    };
    return Identity;
})();
var IdentityEff = function (x) {
    return x;
};
var test = function (v) {
    return function __do() {
        var v1 = v();
        return new Identity(Data_Unit.unit);
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Identity,
    IdentityEff,
    test,
    main
};
