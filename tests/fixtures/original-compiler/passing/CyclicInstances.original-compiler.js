import * as Data_Generic_Rep from "../Data.Generic.Rep/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Show_Generic from "../Data.Show.Generic/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var $runtime_lazy = function (name, moduleName, init) {
    var state = 0;
    var val;
    return function (lineNumber) {
        if (state === 2) return val;
        if (state === 1) throw new ReferenceError(name + " was needed before it finished initializing (module " + moduleName + ", line " + lineNumber + ")", moduleName, lineNumber);
        state = 1;
        val = init();
        state = 2;
        return val;
    };
};
var BIsSymbol = {
    reflectSymbol: function () {
        return "B";
    }
};
var genericShowConstructor = /* #__PURE__ */ Data_Show_Generic.genericShowConstructor(Data_Show_Generic.genericShowArgsNoArguments);
var genericShowConstructor1 = /* #__PURE__ */ genericShowConstructor({
    reflectSymbol: function () {
        return "Z";
    }
});
var B2IsSymbol = {
    reflectSymbol: function () {
        return "B2";
    }
};
var genericShowConstructor2 = /* #__PURE__ */ genericShowConstructor({
    reflectSymbol: function () {
        return "Z2";
    }
});
var A2 = function (x) {
    return x;
};
var B2 = /* #__PURE__ */ (function () {
    function B2(value0) {
        this.value0 = value0;
    };
    B2.create = function (value0) {
        return new B2(value0);
    };
    return B2;
})();
var Z2 = /* #__PURE__ */ (function () {
    function Z2() {

    };
    Z2.value = new Z2();
    return Z2;
})();
var C2 = function (x) {
    return x;
};
var A = function (x) {
    return x;
};
var B = /* #__PURE__ */ (function () {
    function B(value0) {
        this.value0 = value0;
    };
    B.create = function (value0) {
        return new B(value0);
    };
    return B;
})();
var Z = /* #__PURE__ */ (function () {
    function Z() {

    };
    Z.value = new Z();
    return Z;
})();
var C = function (x) {
    return x;
};
var genericC_ = {
    to: function (x) {
        return x;
    },
    from: function (x) {
        return x;
    }
};
var genericC2_ = {
    to: function (x) {
        return x;
    },
    from: function (x) {
        return x;
    }
};
var genericB_ = {
    to: function (x) {
        if (x instanceof Data_Generic_Rep.Inl) {
            return new B(x.value0);
        };
        if (x instanceof Data_Generic_Rep.Inr) {
            return Z.value;
        };
        throw new Error("Failed pattern match at Main (line 13, column 1 - line 13, column 28): " + [ x.constructor.name ]);
    },
    from: function (x) {
        if (x instanceof B) {
            return new Data_Generic_Rep.Inl(x.value0);
        };
        if (x instanceof Z) {
            return new Data_Generic_Rep.Inr(Data_Generic_Rep.NoArguments.value);
        };
        throw new Error("Failed pattern match at Main (line 13, column 1 - line 13, column 28): " + [ x.constructor.name ]);
    }
};
var genericShow = /* #__PURE__ */ Data_Show_Generic.genericShow(genericB_);
var showB = {
    show: function (x) {
        return genericShow(Data_Show_Generic.genericShowSum(Data_Show_Generic.genericShowConstructor(Data_Show_Generic.genericShowArgsArgument($lazy_showC(0)))(BIsSymbol))(genericShowConstructor1))(x);
    }
};
var showA = showB;
var $lazy_showC = /* #__PURE__ */ $runtime_lazy("showC", "Main", function () {
    return {
        show: Data_Show_Generic.genericShow(genericC_)(Data_Show_Generic.genericShowConstructor(Data_Show_Generic.genericShowArgsArgument(showA))({
            reflectSymbol: function () {
                return "C";
            }
        }))
    };
});
var showC = /* #__PURE__ */ $lazy_showC(17);
var genericB2_ = {
    to: function (x) {
        if (x instanceof Data_Generic_Rep.Inl) {
            return new B2(x.value0);
        };
        if (x instanceof Data_Generic_Rep.Inr) {
            return Z2.value;
        };
        throw new Error("Failed pattern match at Main (line 23, column 1 - line 23, column 29): " + [ x.constructor.name ]);
    },
    from: function (x) {
        if (x instanceof B2) {
            return new Data_Generic_Rep.Inl(x.value0);
        };
        if (x instanceof Z2) {
            return new Data_Generic_Rep.Inr(Data_Generic_Rep.NoArguments.value);
        };
        throw new Error("Failed pattern match at Main (line 23, column 1 - line 23, column 29): " + [ x.constructor.name ]);
    }
};
var genericShow1 = /* #__PURE__ */ Data_Show_Generic.genericShow(genericB2_);
var showB2 = {
    show: function (x) {
        return genericShow1(Data_Show_Generic.genericShowSum(Data_Show_Generic.genericShowConstructor(Data_Show_Generic.genericShowArgsArgument($lazy_showC2(0)))(B2IsSymbol))(genericShowConstructor2))(x);
    }
};
var $lazy_showA2 = /* #__PURE__ */ $runtime_lazy("showA2", "Main", function () {
    return Data_Show.showRecord()()(Data_Show.showRecordFieldsConsNil({
        reflectSymbol: function () {
            return "x";
        }
    })(showB2));
});
var $lazy_showC2 = /* #__PURE__ */ $runtime_lazy("showC2", "Main", function () {
    return {
        show: Data_Show_Generic.genericShow(genericC2_)(Data_Show_Generic.genericShowConstructor(Data_Show_Generic.genericShowArgsArgument($lazy_showA2(0)))({
            reflectSymbol: function () {
                return "C2";
            }
        }))
    };
});
var showA2 = /* #__PURE__ */ $lazy_showA2(20);
var showC2 = /* #__PURE__ */ $lazy_showC2(27);
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    A,
    B,
    Z,
    C,
    A2,
    B2,
    Z2,
    C2,
    main,
    showA,
    genericB_,
    showB,
    genericC_,
    showC,
    showA2,
    genericB2_,
    showB2,
    genericC2_,
    showC2
};
