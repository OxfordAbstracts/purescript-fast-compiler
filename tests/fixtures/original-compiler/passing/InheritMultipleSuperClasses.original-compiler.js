import * as Control_Category from "../Control.Category/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var main = /* #__PURE__ */ Effect_Console.log("Done");
var g2 = function (dictEg2) {
    return Data_Functor.map(dictEg2.Functor0())(identity);
};
var g1 = function (dictEg1) {
    return Data_Functor.map(dictEg1.Functor1())(identity);
};
var f2 = function (dictEg2) {
    return Data_Functor.map(dictEg2.Functor1())(identity);
};
var f1 = function (dictEg1) {
    return Data_Functor.map(dictEg1.Functor0())(identity);
};
export {
    f1,
    g1,
    f2,
    g2,
    main
};
