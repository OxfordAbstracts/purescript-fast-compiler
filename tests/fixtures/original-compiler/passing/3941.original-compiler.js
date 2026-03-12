import * as Effect_Console from "../Effect.Console/index.js";
import * as Unsafe_Coerce from "../Unsafe.Coerce/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var func = function (dict) {
    return dict.func;
};
var equals = {
    func: function (a) {
        return a;
    }
};
var testEquals = /* #__PURE__ */ func(equals);
var any = {
    func: Unsafe_Coerce.unsafeCoerce
};
var func1 = /* #__PURE__ */ func(any);
var testAny = func1;
var thisShouldBeCompiled = func1;
export {
    func,
    testEquals,
    testAny,
    thisShouldBeCompiled,
    main,
    equals,
    any
};
