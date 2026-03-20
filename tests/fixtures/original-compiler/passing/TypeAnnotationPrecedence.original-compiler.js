import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Tuple from "../Data.Tuple/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var appendAndLog = /* #__PURE__ */ (function () {
    var $2 = Data_Tuple.uncurry(Data_Semigroup.append(Data_Semigroup.semigroupString));
    return function ($3) {
        return Effect_Console.log($2($3));
    };
})();
var main = /* #__PURE__ */ (function () {
    return appendAndLog(new Data_Tuple.Tuple("Do", "ne"));
})();
export {
    appendAndLog,
    main
};
