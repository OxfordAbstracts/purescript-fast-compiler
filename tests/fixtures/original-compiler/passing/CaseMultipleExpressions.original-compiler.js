import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Partial_Unsafe from "../Partial.Unsafe/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var doIt = /* #__PURE__ */ pure(true);
var set = function __do() {
    Effect_Console.log("Testing...")();
    if (42 === 42 && 10 === 10) {
        return doIt();
    };
    return false;
};
var main = function __do() {
    var b = set();
    if (b) {
        return Effect_Console.log("Done")();
    };
    if (!b) {
        return Partial_Unsafe.unsafeCrashWith("Failed")();
    };
    throw new Error("Failed pattern match at Main (line 19, column 3 - line 21, column 38): " + [ b.constructor.name ]);
};
export {
    doIt,
    set,
    main
};
