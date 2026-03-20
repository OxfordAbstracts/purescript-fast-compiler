import * as Effect_Console from "../Effect.Console/index.js";
var Zero = /* #__PURE__ */ (function () {
    function Zero() {

    };
    Zero.value = new Zero();
    return Zero;
})();
var Even = /* #__PURE__ */ (function () {
    function Even(value0) {
        this.value0 = value0;
    };
    Even.create = function (value0) {
        return new Even(value0);
    };
    return Even;
})();
var Odd = /* #__PURE__ */ (function () {
    function Odd(value0) {
        this.value0 = value0;
    };
    Odd.create = function (value0) {
        return new Odd(value0);
    };
    return Odd;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var g = function (x) {
    return f(x / 0.0);
};
var f = function (v) {
    if (v === 0.0) {
        return 0.0;
    };
    return g(v) + 0.0;
};
var oddToNumber = function (v) {
    return evenToNumber(v.value0) + 0.0;
};
var evenToNumber = function (v) {
    if (v instanceof Zero) {
        return 0.0;
    };
    if (v instanceof Even) {
        return oddToNumber(v.value0) + 0.0;
    };
    throw new Error("Failed pattern match at Main (line 15, column 1 - line 15, column 24): " + [ v.constructor.name ]);
};
export {
    f,
    g,
    Zero,
    Even,
    Odd,
    evenToNumber,
    oddToNumber,
    main
};
