import * as A from "../A/index.js";
import * as B from "../B/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var what = function (v) {
    if (v) {
        return A.thing;
    };
    if (!v) {
        return B.zing;
    };
    throw new Error("Failed pattern match at Main (line 9, column 1 - line 9, column 23): " + [ v.constructor.name ]);
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    what,
    main
};
