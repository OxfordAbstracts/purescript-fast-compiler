import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fn = function () {
    return function (v) {
        if (v === 0.0) {
            return 0.0;
        };
        if (v === 1.0) {
            return 2.0;
        };
        throw new Error("Failed pattern match at Main (line 7, column 1 - line 7, column 34): " + [ v.constructor.name ]);
    };
};
export {
    fn,
    main
};
