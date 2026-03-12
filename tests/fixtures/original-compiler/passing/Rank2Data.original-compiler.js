import * as Effect_Console from "../Effect.Console/index.js";
var Nat = /* #__PURE__ */ (function () {
    function Nat(value0) {
        this.value0 = value0;
    };
    Nat.create = function (value0) {
        return new Nat(value0);
    };
    return Nat;
})();
var Id = /* #__PURE__ */ (function () {
    function Id(value0) {
        this.value0 = value0;
    };
    Id.create = function (value0) {
        return new Id(value0);
    };
    return Id;
})();
var zero$prime = /* #__PURE__ */ (function () {
    return new Nat(function (zero$prime1) {
        return function (v) {
            return zero$prime1;
        };
    });
})();
var succ = function (n) {
    return new Nat(function (zero$prime1) {
        return function (succ1) {
            return succ1(n.value0(zero$prime1)(succ1));
        };
    });
};
var two = /* #__PURE__ */ succ(zero$prime);
var runNat = function (nat) {
    return nat.value0(0.0)(function (n) {
        return n + 1.0;
    });
};
var runId = function (id) {
    return function (a) {
        return id.value0(a);
    };
};
var one$prime = /* #__PURE__ */ succ(zero$prime);
var main = /* #__PURE__ */ Effect_Console.log("Done");
var add = function (n) {
    return function (m) {
        return new Nat(function (zero$prime1) {
            return function (succ1) {
                return m.value0(n.value0(zero$prime1)(succ1))(succ1);
            };
        });
    };
};
var four = /* #__PURE__ */ add(two)(two);
var fourNumber = /* #__PURE__ */ runNat(four);
export {
    Id,
    runId,
    Nat,
    runNat,
    zero$prime,
    succ,
    add,
    one$prime,
    two,
    four,
    fourNumber,
    main
};
