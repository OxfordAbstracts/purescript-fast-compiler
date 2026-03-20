import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);
var compare1 = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordString);
var X = /* #__PURE__ */ (function () {
    function X(value0) {
        this.value0 = value0;
    };
    X.create = function (value0) {
        return new X(value0);
    };
    return X;
})();
var Y = /* #__PURE__ */ (function () {
    function Y(value0) {
        this.value0 = value0;
    };
    Y.create = function (value0) {
        return new Y(value0);
    };
    return Y;
})();
var Z = function (x) {
    return x;
};
var eqX = {
    eq: function (x) {
        return function (y) {
            if (x instanceof X && y instanceof X) {
                return x.value0 === y.value0;
            };
            if (x instanceof Y && y instanceof Y) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};
var eq2 = /* #__PURE__ */ Data_Eq.eq(eqX);
var notEq = /* #__PURE__ */ Data_Eq.notEq(eqX);
var eqZ = {
    eq: function (x) {
        return function (y) {
            return eq2(x.left)(y.left) && eq2(x.right)(y.right);
        };
    }
};
var eq3 = /* #__PURE__ */ Data_Eq.eq(eqZ);
var ordX = {
    compare: function (x) {
        return function (y) {
            if (x instanceof X && y instanceof X) {
                return compare(x.value0)(y.value0);
            };
            if (x instanceof X) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof X) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Y && y instanceof Y) {
                return compare1(x.value0)(y.value0);
            };
            throw new Error("Failed pattern match at Main (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return eqX;
    }
};
var lessThan = /* #__PURE__ */ Data_Ord.lessThan(ordX);
var main = /* #__PURE__ */ (function () {
    var z = {
        left: new X(0),
        right: new Y("Foo")
    };
    return function __do() {
        Test_Assert.assert(eq2(new X(0))(new X(0)))();
        Test_Assert.assert(notEq(new X(0))(new X(1)))();
        Test_Assert.assert(eq2(new Y("Foo"))(new Y("Foo")))();
        Test_Assert.assert(notEq(new Y("Foo"))(new Y("Bar")))();
        Test_Assert.assert(lessThan(new X(0))(new X(1)))();
        Test_Assert.assert(lessThan(new X(0))(new Y("Foo")))();
        Test_Assert.assert(lessThan(new Y("Bar"))(new Y("Baz")))();
        Test_Assert.assert(eq3(z)(z))();
        return Effect_Console.log("Done")();
    };
})();
var eqV = {
    eq: function (x) {
        return function (y) {
            return false;
        };
    }
};
var ordV = {
    compare: function (x) {
        return function (y) {
            return Data_Ordering.EQ.value;
        };
    },
    Eq0: function () {
        return eqV;
    }
};
export {
    X,
    Y,
    Z,
    main,
    eqV,
    ordV,
    eqX,
    ordX,
    eqZ
};
