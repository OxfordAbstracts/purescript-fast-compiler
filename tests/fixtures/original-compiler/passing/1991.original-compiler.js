import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var singleton = function (x) {
    return [ x ];
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foldMap = function (dictSemigroup) {
    var append = Data_Semigroup.append(dictSemigroup);
    return function (v) {
        return function (v1) {
            if (v1.length === 5) {
                return append(v(v1[0]))(append(v(v1[1]))(append(v(v1[2]))(append(v(v1[3]))(v(v1[4])))));
            };
            return foldMap(dictSemigroup)(v)(v1);
        };
    };
};
var empty = [  ];
var regression = /* #__PURE__ */ (function () {
    var as = [ 1, 2, 3, 4, 5 ];
    var as$prime = foldMap(Data_Semigroup.semigroupArray)(function (x) {
        var $14 = 1 < x && x < 4;
        if ($14) {
            return singleton(x);
        };
        return empty;
    })(as);
    return as$prime;
})();
export {
    singleton,
    empty,
    foldMap,
    regression,
    main
};
