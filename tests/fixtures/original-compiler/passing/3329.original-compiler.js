import * as Data_Either from "../Data.Either/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var prj = function (dict) {
    return dict.prj;
};
var injectRefl = {
    inj: function (x) {
        return x;
    },
    prj: function (x) {
        return new Data_Maybe.Just(x);
    }
};
var injectLeft = {
    inj: function (x) {
        return new Data_Either.Left(x);
    },
    prj: function (v) {
        if (v instanceof Data_Either.Left) {
            return new Data_Maybe.Just(v.value0);
        };
        return Data_Maybe.Nothing.value;
    }
};
var inj = function (dict) {
    return dict.inj;
};
var inj1 = /* #__PURE__ */ inj(injectLeft);
var injL = inj1;
var injectRight = function (dictInject) {
    var inj2 = inj(dictInject);
    var prj1 = prj(dictInject);
    return {
        inj: function (x) {
            return new Data_Either.Right(inj2(x));
        },
        prj: function (v) {
            if (v instanceof Data_Either.Right) {
                return prj1(v.value0);
            };
            return Data_Maybe.Nothing.value;
        }
    };
};
var main = /* #__PURE__ */ (function () {
    var testInjLWithUnknowns = function (a) {
        var v = inj1(a);
        if (v instanceof Data_Either.Left) {
            return v.value0;
        };
        if (v instanceof Data_Either.Right) {
            return a;
        };
        throw new Error("Failed pattern match at Main (line 32, column 28 - line 34, column 17): " + [ v.constructor.name ]);
    };
    return Effect_Console.log("Done");
})();
export {
    inj,
    prj,
    injL,
    main,
    injectRefl,
    injectLeft,
    injectRight
};
