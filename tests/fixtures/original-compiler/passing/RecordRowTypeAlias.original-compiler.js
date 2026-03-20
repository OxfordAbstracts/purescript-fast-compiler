import * as $foreign from "./foreign.js";
import * as Effect_Console from "../Effect.Console/index.js";
var merge = function () {
    return function (v) {
        return function (v1) {
            return $foreign.unsafeCoerce(0);
        };
    };
};
var merge1 = /* #__PURE__ */ merge();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var identity$prime = function (x) {
    return x;
};
var test = function () {
    return function (a) {
        return function (b) {
            return identity$prime(merge1(a)(b));
        };
    };
};
export {
    unsafeCoerce
} from "./foreign.js";
export {
    merge,
    identity$prime,
    test,
    main
};
