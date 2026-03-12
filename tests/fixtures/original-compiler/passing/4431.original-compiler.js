import * as Data_Functor from "../Data.Functor/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var Get = /* #__PURE__ */ (function () {
    function Get(value0) {
        this.value0 = value0;
    };
    Get.create = function (value0) {
        return new Get(value0);
    };
    return Get;
})();
var functorTypedCache = function (dictFunctor) {
    var map = Data_Functor.map(dictFunctor);
    return {
        map: function (f) {
            return function (m) {
                return new Get(map(f)(m.value0));
            };
        }
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Get,
    main,
    functorTypedCache
};
