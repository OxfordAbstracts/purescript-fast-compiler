import * as Data_Functor from "../Data.Functor/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var map$prime = function (dictFunctor) {
    return Data_Functor.map(dictFunctor);
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var identity = function (x) {
    return x;
};
export {
    identity,
    map$prime,
    main
};
