import * as Effect_Console from "../Effect.Console/index.js";
import * as GivenConstraintScoped_Lib from "../GivenConstraintScoped.Lib/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var handler = function (dictCl) {
    var member = GivenConstraintScoped_Lib.member(dictCl.Super0());
    return function (key) {
        return member(key);
    };
};
export {
    handler,
    main
};
