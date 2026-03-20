import * as Data_Generic_Rep from "../Data.Generic.Rep/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Lib from "../Lib/index.js";
var GenericFoo = /* #__PURE__ */ (function () {
    function GenericFoo() {

    };
    GenericFoo.value = new GenericFoo();
    return GenericFoo;
})();
var Left = /* #__PURE__ */ (function () {
    function Left(value0) {
        this.value0 = value0;
    };
    Left.create = function (value0) {
        return new Left(value0);
    };
    return Left;
})();
var Right = /* #__PURE__ */ (function () {
    function Right(value0) {
        this.value0 = value0;
    };
    Right.create = function (value0) {
        return new Right(value0);
    };
    return Right;
})();
var Foo = /* #__PURE__ */ (function () {
    function Foo(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Foo.create = function (value0) {
        return function (value1) {
            return new Foo(value0, value1);
        };
    };
    return Foo;
})();
var reservedWordFunction = {};
var reservedWordArrow = {};
var overlappingStillCompiles = {};
var overlappingStillCompiles1 = {};
var oneTypeParamChainString = {};
var oneTypeParamChainBoolean = {};
var oneTypeParamBoolean = {};
var noTypeParams = {};
var multipleTypeParamsChainBo = {};
var multipleTypeParamsChainBo1 = {};
var multipleTypeParamsChainBo2 = {};
var multipleTypeParamsChainBo3 = {};
var multipleTypeParamsChainBo4 = {};
var multipleTypeParamsBoolean = {};
var multipleKindParamsConstru = {};
var multipleKindParamsChainCo = {};
var multipleKindParamsChainCo1 = {};
var multipleKindParamsChainCo2 = {};
var higherKindedTypeParamsCha = {
    hktpChain: function (v) {
        return function (v1) {
            return 0;
        };
    }
};
var higherKindedTypeParamsCha1 = {
    hktpChain: function (v) {
        return function (v1) {
            return 0;
        };
    }
};
var higherKindedTypeParamsArr = {
    hktp: function (v) {
        return function (v1) {
            return 0;
        };
    }
};
var genericGenericFoo_ = {
    to: function (x) {
        return GenericFoo.value;
    },
    from: function (x) {
        return Data_Generic_Rep.NoArguments.value;
    }
};
var main = function __do() {
    Lib.namedExportStillWorksUnit(0)();
    return Effect_Console.log("Done")();
};
var hktpChain = function (dict) {
    return dict.hktpChain;
};
var hktp = function (dict) {
    return dict.hktp;
};
export {
    hktp,
    hktpChain,
    Foo,
    GenericFoo,
    main,
    Left,
    Right,
    noTypeParams,
    oneTypeParamBoolean,
    oneTypeParamChainBoolean,
    oneTypeParamChainString,
    multipleTypeParamsBoolean,
    multipleTypeParamsChainBo4,
    multipleTypeParamsChainBo3,
    multipleTypeParamsChainBo2,
    multipleTypeParamsChainBo1,
    multipleTypeParamsChainBo,
    higherKindedTypeParamsArr,
    higherKindedTypeParamsCha1,
    higherKindedTypeParamsCha,
    multipleKindParamsConstru,
    multipleKindParamsChainCo2,
    multipleKindParamsChainCo1,
    multipleKindParamsChainCo,
    reservedWordArrow,
    reservedWordFunction,
    genericGenericFoo_,
    overlappingStillCompiles1,
    overlappingStillCompiles
};
