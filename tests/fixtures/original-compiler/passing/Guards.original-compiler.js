import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingNumber);
var testIndentation = function (x) {
    return function (y) {
        if (x > 0.0) {
            return x + y;
        };
        if (Data_Boolean.otherwise) {
            return y - x;
        };
        throw new Error("Failed pattern match at Main (line 24, column 1 - line 24, column 46): " + [ x.constructor.name, y.constructor.name ]);
    };
};
var min = function (dictOrd) {
    var lessThan = Data_Ord.lessThan(dictOrd);
    return function (n) {
        return function (m) {
            if (lessThan(n)(m)) {
                return n;
            };
            if (Data_Boolean.otherwise) {
                return m;
            };
            throw new Error("Failed pattern match at Main (line 15, column 1 - line 15, column 38): " + [ n.constructor.name, m.constructor.name ]);
        };
    };
};
var max = function (dictOrd) {
    var lessThan = Data_Ord.lessThan(dictOrd);
    return function (n) {
        return function (m) {
            if (lessThan(m)(n)) {
                return n;
            };
            if (Data_Boolean.otherwise) {
                return m;
            };
            throw new Error("Failed pattern match at Main (line 20, column 11 - line 22, column 21): " + [ Data_Unit.unit.constructor.name ]);
        };
    };
};
var max1 = /* #__PURE__ */ max(Data_Ord.ordInt);
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ min(Data_Ord.ordString)("Done")("ZZZZ"));
var collatz2 = function (x) {
    return function (y) {
        if (y > 0.0) {
            return x / 2.0;
        };
        return x * 3.0 + 1.0;
    };
};
var collatz = function (x) {
    if (mod(x)(2.0) === 0.0) {
        return x / 2.0;
    };
    return x * 3.0 + 1.0;
};
var clunky_case2 = function (a) {
    return function (b) {
        var v = function (v1) {
            if (Data_Boolean.otherwise) {
                return a + b | 0;
            };
            throw new Error("Failed pattern match at Main (line 60, column 1 - line 60, column 34): " + [ Data_Unit.unit.constructor.name ]);
        };
        var $38 = max1(a)(b);
        var $39 = $38 > 5;
        if ($39) {
            return $38;
        };
        return v(true);
    };
};
var clunky_case1 = function (a) {
    return function (b) {
        var v = function (v1) {
            if (Data_Boolean.otherwise) {
                return a + b | 0;
            };
            throw new Error("Failed pattern match at Main (line 51, column 1 - line 51, column 34): " + [ Data_Unit.unit.constructor.name ]);
        };
        var $42 = max1(a)(b);
        var $43 = $42 > 5;
        if ($43) {
            return $42;
        };
        return v(true);
    };
};
var clunky2 = function (a) {
    return function (b) {
        var v = function (v1) {
            if (Data_Boolean.otherwise) {
                return a + b | 0;
            };
            throw new Error("Failed pattern match at Main (line 43, column 1 - line 43, column 29): " + [ a.constructor.name, b.constructor.name ]);
        };
        var $48 = max1(a)(b);
        var $49 = $48 > 5;
        if ($49) {
            return $48;
        };
        return v(true);
    };
};
var clunky1_refutable = function (v) {
    return function (v1) {
        var v2 = function (v3) {
            return v;
        };
        if (v === 0) {
            var $54 = max1(v1)(v1);
            var $55 = $54 > 5;
            if ($55) {
                return $54;
            };
            return v2(true);
        };
        return v2(true);
    };
};
var clunky1 = function (v) {
    return function (v1) {
        var v2 = function (v3) {
            return v;
        };
        var $60 = max1(v)(v1);
        var $61 = $60 > 5;
        if ($61) {
            return $60;
        };
        return v2(true);
    };
};
export {
    collatz,
    collatz2,
    min,
    max,
    testIndentation,
    clunky1,
    clunky1_refutable,
    clunky2,
    clunky_case1,
    clunky_case2,
    main
};
