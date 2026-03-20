import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var assertIsGTGT = {
    assertIsGT: function (v) {
        return true;
    }
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var assertLesser = function () {
    return $$Proxy.value;
};
var assertLesser1 = /* #__PURE__ */ assertLesser();
var litLt = assertLesser1;
var litTransLT = function () {
    return assertLesser1;
};
var litTransRange = function () {
    return function () {
        return assertLesser1;
    };
};
var symmLt = function () {
    return assertLesser1;
};
var transEqLt = function () {
    return function () {
        return function (v) {
            return assertLesser1;
        };
    };
};
var transLt = function () {
    return function () {
        return function (v) {
            return assertLesser1;
        };
    };
};
var transLtEq = function () {
    return function () {
        return function (v) {
            return assertLesser1;
        };
    };
};
var transSymmEqLt = function () {
    return function () {
        return function (v) {
            return assertLesser1;
        };
    };
};
var transSymmLt = function () {
    return function () {
        return function (v) {
            return assertLesser1;
        };
    };
};
var transSymmLtEq = function () {
    return function () {
        return function (v) {
            return assertLesser1;
        };
    };
};
var withFacts = function () {
    return function () {
        return assertLesser1;
    };
};
var assertIsGT = function (dict) {
    return dict.assertIsGT;
};
var infer = function () {
    return function (dictAssertIsGT) {
        var assertIsGT1 = assertIsGT(dictAssertIsGT);
        return function (v) {
            return function (v1) {
                return assertIsGT1($$Proxy.value);
            };
        };
    };
};
var infer1 = /* #__PURE__ */ infer()(assertIsGTGT);
var inferSolved = function () {
    return function () {
        return function (m) {
            return function (v) {
                return function (p) {
                    return infer1(m)(p);
                };
            };
        };
    };
};
var assertGreater = function () {
    return $$Proxy.value;
};
var assertGreater1 = /* #__PURE__ */ assertGreater();
var litGt = assertGreater1;
var litTransGT = function () {
    return assertGreater1;
};
var symmGt = function () {
    return assertGreater1;
};
var transEqGt = function () {
    return function () {
        return function (v) {
            return assertGreater1;
        };
    };
};
var transGt = function () {
    return function () {
        return function (v) {
            return assertGreater1;
        };
    };
};
var transGtEq = function () {
    return function () {
        return function (v) {
            return assertGreater1;
        };
    };
};
var transSymmEqGt = function () {
    return function () {
        return function (v) {
            return assertGreater1;
        };
    };
};
var transSymmGt = function () {
    return function () {
        return function (v) {
            return assertGreater1;
        };
    };
};
var transSymmGtEq = function () {
    return function () {
        return function (v) {
            return assertGreater1;
        };
    };
};
var assertEqual = function () {
    return $$Proxy.value;
};
var assertEqual1 = /* #__PURE__ */ assertEqual();
var litEq = assertEqual1;
var reflEq = assertEqual1;
var symmEq = function () {
    return assertEqual1;
};
var transEq = function () {
    return function () {
        return function (v) {
            return assertEqual1;
        };
    };
};
var transSymmEq = function () {
    return function () {
        return function (v) {
            return assertEqual1;
        };
    };
};
export {
    assertIsGT,
    $$Proxy as Proxy,
    assertLesser,
    assertGreater,
    assertEqual,
    symmLt,
    symmGt,
    symmEq,
    reflEq,
    transLt,
    transLtEq,
    transEqLt,
    transGt,
    transGtEq,
    transEqGt,
    transEq,
    transSymmLt,
    transSymmLtEq,
    transSymmEqLt,
    transSymmGt,
    transSymmGtEq,
    transSymmEqGt,
    transSymmEq,
    litLt,
    litGt,
    litEq,
    infer,
    inferSolved,
    litTransLT,
    litTransGT,
    litTransRange,
    withFacts,
    main,
    assertIsGTGT
};
