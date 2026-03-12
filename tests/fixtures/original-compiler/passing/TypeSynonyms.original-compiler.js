import * as Effect_Console from "../Effect.Console/index.js";
var N = function (x) {
    return x;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fst = {
    get: function (p) {
        return p.fst;
    },
    set: function (p) {
        return function (a) {
            return {
                fst: a,
                snd: p.snd
            };
        };
    }
};
var composeLenses = function (l1) {
    return function (l2) {
        return {
            get: function (a) {
                return l2.get(l1.get(a));
            },
            set: function (a) {
                return function (c) {
                    return l1.set(a)(l2.set(l1.get(a))(c));
                };
            }
        };
    };
};
var test1 = /* #__PURE__ */ composeLenses(fst)(fst);
export {
    composeLenses,
    fst,
    test1,
    N,
    main
};
