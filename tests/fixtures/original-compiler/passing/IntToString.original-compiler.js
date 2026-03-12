import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var testToString = function () {
    return function (v) {
        return $$Proxy.value;
    };
};
var testToString1 = /* #__PURE__ */ testToString();
var zeroToString = /* #__PURE__ */ (function () {
    return testToString1($$Proxy.value);
})();
var zeroToStringTA = /* #__PURE__ */ (function () {
    return testToString1($$Proxy.value);
})();
var posToStringTA = /* #__PURE__ */ (function () {
    return testToString1($$Proxy.value);
})();
var posToString = /* #__PURE__ */ (function () {
    return testToString1($$Proxy.value);
})();
var negToStringTA = /* #__PURE__ */ (function () {
    return testToString1($$Proxy.value);
})();
var negToString = /* #__PURE__ */ (function () {
    return testToString1($$Proxy.value);
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var intMul = function () {
    return function (v) {
        return function (v1) {
            return $$Proxy.value;
        };
    };
};
var intMul1 = /* #__PURE__ */ intMul();
var testMul = /* #__PURE__ */ (function () {
    return testToString1(intMul1($$Proxy.value)($$Proxy.value));
})();
var intAdd = function () {
    return function (v) {
        return function (v1) {
            return $$Proxy.value;
        };
    };
};
var intAdd1 = /* #__PURE__ */ intAdd();
var testAdd = /* #__PURE__ */ (function () {
    return testToString1(intAdd1($$Proxy.value)($$Proxy.value));
})();
var testAddMul = /* #__PURE__ */ (function () {
    return testToString1(intMul1($$Proxy.value)(intAdd1($$Proxy.value)($$Proxy.value)));
})();
var testMulAdd = /* #__PURE__ */ (function () {
    return testToString1(intAdd1($$Proxy.value)(intMul1($$Proxy.value)($$Proxy.value)));
})();
var _maxInt = /* #__PURE__ */ (function () {
    return $$Proxy.value;
})();
var testBeyondMax = /* #__PURE__ */ (function () {
    return testToString1(intMul1(_maxInt)($$Proxy.value));
})();
var testMax = /* #__PURE__ */ testToString1(_maxInt);
export {
    $$Proxy as Proxy,
    testToString,
    posToString,
    negToString,
    zeroToString,
    posToStringTA,
    negToStringTA,
    zeroToStringTA,
    intAdd,
    intMul,
    testAdd,
    testMul,
    testMulAdd,
    testAddMul,
    _maxInt,
    testMax,
    testBeyondMax,
    main
};
