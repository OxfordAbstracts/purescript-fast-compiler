import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var snd = function () {
    return function (v) {
        if (v.length === 2) {
            return v[1];
        };
        throw new Error("Failed pattern match at Main (line 10, column 7 - line 10, column 19): " + [ v.constructor.name ]);
    };
};
var snd1 = /* #__PURE__ */ snd();
var main = /* #__PURE__ */ (function () {
    var ts = snd1([ 1.0, 2.0 ]);
    return function __do() {
        Test_Assert["assert$prime"]("Incorrect result from 'snd'.")(ts === 2.0)();
        return Effect_Console.log("Done")();
    };
})();
export {
    snd,
    main
};
