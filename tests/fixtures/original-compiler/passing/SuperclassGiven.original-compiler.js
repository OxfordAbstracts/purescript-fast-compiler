import * as Effect_Console from "../Effect.Console/index.js";
import * as SuperclassGiven_Lib from "../SuperclassGiven.Lib/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var handler = function (dictCl) {
    var member = SuperclassGiven_Lib.member(dictCl.Super0());
    return function (key) {
        return member({
            key: key
        });
    };
};
export {
    handler,
    main
};
