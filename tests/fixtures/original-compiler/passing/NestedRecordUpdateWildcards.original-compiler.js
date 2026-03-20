import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var update = function (v) {
    return function (v1) {
        return function (v2) {
            return function (v3) {
                var $18 = {};
                for (var $19 in v) {
                    if ({}.hasOwnProperty.call(v, $19)) {
                        $18[$19] = v[$19];
                    };
                };
                $18.foo = v1;
                $18.bar = (function () {
                    var $15 = {};
                    for (var $16 in v.bar) {
                        if ({}.hasOwnProperty.call(v.bar, $16)) {
                            $15[$16] = v["bar"][$16];
                        };
                    };
                    $15.baz = v2;
                    $15.qux = v3;
                    return $15;
                })();
                return $18;
            };
        };
    };
};
var init = {
    foo: 1,
    bar: {
        baz: 2,
        qux: 3
    }
};
var expected = {
    foo: 10,
    bar: {
        baz: 20,
        qux: 30
    }
};
var check = function (dictEq) {
    var eq = Data_Eq.eq(dictEq);
    return function (dictEq1) {
        var eq1 = Data_Eq.eq(dictEq1);
        return function (dictEq2) {
            var eq2 = Data_Eq.eq(dictEq2);
            return function (l) {
                return function (r) {
                    return eq(l.foo)(r.foo) && (eq1(l.bar.baz)(r.bar.baz) && eq2(l.bar.qux)(r.bar.qux));
                };
            };
        };
    };
};
var after = /* #__PURE__ */ update(init)(10)(20)(30);
var main = /* #__PURE__ */ Control_Applicative.when(Effect.applicativeEffect)(/* #__PURE__ */ check(Data_Eq.eqInt)(Data_Eq.eqInt)(Data_Eq.eqInt)(after)(expected))(/* #__PURE__ */ Effect_Console.log("Done"));
export {
    update,
    init,
    after,
    expected,
    check,
    main
};
