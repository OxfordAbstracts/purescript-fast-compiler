import * as $foreign from "./foreign.js";
import * as Effect_Console from "../Effect.Console/index.js";
var partial = function () {
    return function (n) {
        if (n === 0) {
            return 0;
        };
        throw new Error("Failed pattern match at Main (line 7, column 13 - line 8, column 9): " + [ n.constructor.name ]);
    };
};
var partial1 = /* #__PURE__ */ partial();
var otherDischargePartial = $foreign["_otherDischargePartial"];
var unsafeOp = /* #__PURE__ */ otherDischargePartial(function () {
    return partial1;
});
var main = /* #__PURE__ */ (function () {
    var v = unsafeOp(0);
    return Effect_Console.log("Done");
})();
export {
    _otherDischargePartial
} from "./foreign.js";
export {
    partial,
    unsafeOp,
    otherDischargePartial,
    main
};
