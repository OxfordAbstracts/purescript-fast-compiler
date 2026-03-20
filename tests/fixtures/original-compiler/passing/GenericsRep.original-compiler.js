import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Eq_Generic from "../Data.Eq.Generic/index.js";
import * as Data_Generic_Rep from "../Data.Generic.Rep/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var genericEqSum = /* #__PURE__ */ Data_Eq_Generic.genericEqSum(/* #__PURE__ */ Data_Eq_Generic.genericEqConstructor(Data_Eq_Generic.genericEqNoArguments));
var logShow = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showBoolean);
var Y = /* #__PURE__ */ (function () {
    function Y() {

    };
    Y.value = new Y();
    return Y;
})();
var Z = /* #__PURE__ */ (function () {
    function Z(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Z.create = function (value0) {
        return function (value1) {
            return new Z(value0, value1);
        };
    };
    return Z;
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
var W = function (x) {
    return x;
};
var genericZ = {
    to: function (x) {
        return Data_Generic_Rep.to(genericZ)(x);
    },
    from: function (x) {
        return Data_Generic_Rep.from(genericZ)(x);
    }
};
var genericEq = /* #__PURE__ */ Data_Eq_Generic.genericEq(genericZ)(Data_Eq_Generic.genericEqNoConstructors);
var genericY = {
    to: function (x) {
        if (x instanceof Data_Generic_Rep.Inl) {
            return Y.value;
        };
        if (x instanceof Data_Generic_Rep.Inr) {
            return new Z(x.value0.value0, x.value0.value1);
        };
        throw new Error("Failed pattern match at Main (line 18, column 1 - line 18, column 44): " + [ x.constructor.name ]);
    },
    from: function (x) {
        if (x instanceof Y) {
            return new Data_Generic_Rep.Inl(Data_Generic_Rep.NoArguments.value);
        };
        if (x instanceof Z) {
            return new Data_Generic_Rep.Inr(new Data_Generic_Rep.Product(x.value0, x.value1));
        };
        throw new Error("Failed pattern match at Main (line 18, column 1 - line 18, column 44): " + [ x.constructor.name ]);
    }
};
var genericEq1 = /* #__PURE__ */ Data_Eq_Generic.genericEq(genericY);
var genericX = {
    to: function (x) {
        return new X(x);
    },
    from: function (x) {
        return x.value0;
    }
};
var genericEq2 = /* #__PURE__ */ Data_Eq_Generic.genericEq(genericX);
var genericW = {
    to: function (x) {
        return x;
    },
    from: function (x) {
        return x;
    }
};
var eqZ = {
    eq: function (x) {
        return function (y) {
            return genericEq(x)(y);
        };
    }
};
var eqY = function (dictEq) {
    var genericEqProduct = Data_Eq_Generic.genericEqProduct(Data_Eq_Generic.genericEqArgument(dictEq));
    return {
        eq: function (xs) {
            return function (ys) {
                return genericEq1(genericEqSum(Data_Eq_Generic.genericEqConstructor(genericEqProduct(Data_Eq_Generic.genericEqArgument(eqY(dictEq))))))(xs)(ys);
            };
        }
    };
};
var eq = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ eqY(Data_Eq.eqInt));
var eq1 = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ eqY(eqZ));
var eqX = function (dictEq) {
    var genericEq3 = genericEq2(Data_Eq_Generic.genericEqConstructor(Data_Eq_Generic.genericEqArgument(dictEq)));
    return {
        eq: function (xs) {
            return function (ys) {
                return genericEq3(xs)(ys);
            };
        }
    };
};
var eq2 = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ eqX(Data_Eq.eqInt));
var main = function __do() {
    logShow(eq2(new X(0))(new X(1)))();
    logShow(eq2(new X(1))(new X(1)))();
    logShow(eq(new Z(1, Y.value))(new Z(1, Y.value)))();
    logShow(eq(new Z(1, Y.value))(Y.value))();
    logShow(eq1(Y.value)(Y.value))();
    return Effect_Console.log("Done")();
};
export {
    X,
    Y,
    Z,
    W,
    main,
    genericX,
    eqX,
    genericY,
    eqY,
    genericZ,
    eqZ,
    genericW
};
