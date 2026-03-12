import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var init = {
    foo: 1,
    bar: {
        baz: 2,
        qux: {
            lhs: 3,
            rhs: 4
        }
    }
};
var updated = {
    foo: 10,
    bar: {
        baz: 20,
        qux: {
            lhs: 30,
            rhs: 40
        }
    }
};
var expected = {
    foo: 10,
    bar: {
        baz: 20,
        qux: {
            lhs: 30,
            rhs: 40
        }
    }
};
var check = function (dictEq) {
    var eq = Data_Eq.eq(dictEq);
    return function (dictEq1) {
        var eq1 = Data_Eq.eq(dictEq1);
        return function (dictEq2) {
            var eq2 = Data_Eq.eq(dictEq2);
            return function (dictEq3) {
                var eq3 = Data_Eq.eq(dictEq3);
                return function (l) {
                    return function (r) {
                        return eq(l.foo)(r.foo) && (eq1(l.bar.baz)(r.bar.baz) && (eq2(l.bar.qux.lhs)(r.bar.qux.lhs) && eq3(l.bar.qux.rhs)(r.bar.qux.rhs)));
                    };
                };
            };
        };
    };
};
var main = /* #__PURE__ */ Control_Applicative.when(Effect.applicativeEffect)(/* #__PURE__ */ check(Data_Eq.eqInt)(Data_Eq.eqInt)(Data_Eq.eqInt)(Data_Eq.eqInt)(updated)(expected))(/* #__PURE__ */ Effect_Console.log("Done"));
export {
    init,
    updated,
    expected,
    check,
    main
};
