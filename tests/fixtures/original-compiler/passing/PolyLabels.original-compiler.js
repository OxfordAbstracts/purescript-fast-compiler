import * as $foreign from "./foreign.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Symbol from "../Data.Symbol/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var fooIsSymbol = {
    reflectSymbol: function () {
        return "foo";
    }
};
var set = function (dictIsSymbol) {
    var reflectSymbol = Data_Symbol.reflectSymbol(dictIsSymbol);
    return function () {
        return function () {
            return function (l) {
                return $foreign.unsafeSet(reflectSymbol(l));
            };
        };
    };
};
var setFoo = /* #__PURE__ */ (function () {
    return set(fooIsSymbol)()()(Type_Proxy["Proxy"].value);
})();
var get = function (dictIsSymbol) {
    var reflectSymbol = Data_Symbol.reflectSymbol(dictIsSymbol);
    return function () {
        return function (l) {
            return $foreign.unsafeGet(reflectSymbol(l));
        };
    };
};
var getFoo = /* #__PURE__ */ (function () {
    return get(fooIsSymbol)()(Type_Proxy["Proxy"].value);
})();
var lens = function (dictIsSymbol) {
    var set1 = set(dictIsSymbol)()();
    var get1 = get(dictIsSymbol)();
    return function () {
        return function () {
            return function (dictFunctor) {
                var map = Data_Functor.map(dictFunctor);
                return function (l) {
                    return function (f) {
                        return function (r) {
                            return map(Data_Function.flip(set1(l))(r))(f(get1(l)(r)));
                        };
                    };
                };
            };
        };
    };
};
var lens1 = /* #__PURE__ */ lens(fooIsSymbol)()();
var fooLens = function (dictFunctor) {
    return lens1(dictFunctor)(Type_Proxy["Proxy"].value);
};
var main = function __do() {
    fooLens(Effect.functorEffect)(Effect_Console.logShow(Data_Show.showInt))({
        foo: 1
    })();
    return Effect_Console.log(getFoo(setFoo("Done")({
        foo: 1
    })))();
};
export {
    unsafeGet,
    unsafeSet
} from "./foreign.js";
export {
    get,
    set,
    lens,
    getFoo,
    setFoo,
    fooLens,
    main
};
