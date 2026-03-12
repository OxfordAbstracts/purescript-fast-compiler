import * as Effect_Console from "../Effect.Console/index.js";
import * as Safe_Coerce from "../Safe.Coerce/index.js";
var coerce = /* #__PURE__ */ Safe_Coerce.coerce();
var Name = function (x) {
    return x;
};
var MyFunctor = function (x) {
    return x;
};
var myCoerce = function () {
    return coerce;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var getName = /* #__PURE__ */ myCoerce();
export {
    MyFunctor,
    myCoerce,
    Name,
    getName,
    main
};
