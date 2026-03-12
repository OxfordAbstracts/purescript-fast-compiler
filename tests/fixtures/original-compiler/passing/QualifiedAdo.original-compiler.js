import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Apply from "../Control.Apply/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as IxApplicative from "../IxApplicative/index.js";
var testIApplicative = function (dictIxApplicative) {
    var pure = IxApplicative.pure(dictIxApplicative);
    return IxApplicative.apply(dictIxApplicative)(IxApplicative.map(dictIxApplicative.IxFunctor0())(function (v) {
        return function (v1) {
            return v + v1;
        };
    })(pure("test")))(pure("test"));
};
var testApplicative = function (dictApplicative) {
    var Apply0 = dictApplicative.Apply0();
    var pure = Control_Applicative.pure(dictApplicative);
    return Control_Apply.apply(Apply0)(Data_Functor.map(Apply0.Functor0())(function (v) {
        return function (v1) {
            return v + v1;
        };
    })(pure("test")))(pure("test"));
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    testIApplicative,
    testApplicative,
    main
};
