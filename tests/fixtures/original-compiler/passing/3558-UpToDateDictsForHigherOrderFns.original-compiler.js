import * as Data_Symbol from "../Data.Symbol/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Record_Unsafe from "../Record.Unsafe/index.js";
var LBox = function (x) {
    return x;
};
var unLBox = function (g) {
    return function (v) {
        var g2 = g();
        return v(function () {
            return function (dictIsSymbol) {
                return g2(dictIsSymbol);
            };
        });
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var lboxIdentity = /* #__PURE__ */ unLBox(function () {
    return function (dictIsSymbol) {
        return function (lbl) {
            return function (f) {
                return f()(dictIsSymbol)(lbl);
            };
        };
    };
});
var get = function (dictIsSymbol) {
    var reflectSymbol = Data_Symbol.reflectSymbol(dictIsSymbol);
    return function () {
        return function (l) {
            return function (r) {
                return Record_Unsafe.unsafeGet(reflectSymbol(l))(r);
            };
        };
    };
};
var read = function (rec) {
    return unLBox(function () {
        return function (dictIsSymbol) {
            var get1 = get(dictIsSymbol)();
            return function (lbl) {
                return get1(lbl)(rec);
            };
        };
    });
};
export {
    LBox,
    unLBox,
    lboxIdentity,
    read,
    get,
    main
};
