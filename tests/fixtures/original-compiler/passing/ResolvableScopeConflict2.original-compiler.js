import * as A from "../A/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var thing = 1;
var what = function (v) {
    if (v) {
        return thing;
    };
    if (!v) {
        return A.zing;
    };
    throw new Error("Failed pattern match at Main (line 11, column 1 - line 11, column 23): " + [ v.constructor.name ]);
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    thing,
    what,
    main
};
