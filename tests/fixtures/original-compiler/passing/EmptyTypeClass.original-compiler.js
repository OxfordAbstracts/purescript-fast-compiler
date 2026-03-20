import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var head = function () {
    return function (v) {
        if (v.length === 1) {
            return v[0];
        };
        throw new Error("Failed pattern match at Main (line 7, column 1 - line 7, column 42): " + [ v.constructor.name ]);
    };
};
export {
    head,
    main
};
