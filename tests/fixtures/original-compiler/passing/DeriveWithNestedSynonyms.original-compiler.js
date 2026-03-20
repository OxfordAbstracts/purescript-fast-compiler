import * as Data_Ord from "../Data.Ord/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordString);
var Z = /* #__PURE__ */ (function () {
    function Z(value0) {
        this.value0 = value0;
    };
    Z.create = function (value0) {
        return new Z(value0);
    };
    return Z;
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
var X = /* #__PURE__ */ (function () {
    function X(value0) {
        this.value0 = value0;
    };
    X.create = function (value0) {
        return new X(value0);
    };
    return X;
})();
var T = function (x) {
    return x;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var eqZ = {
    eq: function (x) {
        return function (y) {
            return true;
        };
    }
};
var eqY = {
    eq: function (x) {
        return function (y) {
            return true;
        };
    }
};
var eqX = {
    eq: function (x) {
        return function (y) {
            return true;
        };
    }
};
var eqT = {
    eq: function (x) {
        return function (y) {
            return x.baz.foo === y.baz.foo;
        };
    }
};
var ordT = {
    compare: function (x) {
        return function (y) {
            return compare(x.baz.foo)(y.baz.foo);
        };
    },
    Eq0: function () {
        return eqT;
    }
};
export {
    X,
    Y,
    Z,
    T,
    main,
    eqX,
    eqY,
    eqZ,
    eqT,
    ordT
};
