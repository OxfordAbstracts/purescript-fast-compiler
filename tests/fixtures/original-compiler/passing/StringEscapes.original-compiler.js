import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var surrogatePair = /* #__PURE__ */ (function () {
    return "\ud834\udf06" === "\ud834\udf06";
})();
var singleCharacter = /* #__PURE__ */ (function () {
    return "\x09\x0a\x0d\"\\" === "\x09\x0a\x0d\"\\";
})();
var replacement = "\ufffd";
var lowSurrogate = "\udf06";
var highSurrogate = "\ud834";
var loneSurrogates = /* #__PURE__ */ (function () {
    return highSurrogate + lowSurrogate === "\ud834\udf06";
})();
var notReplacing = /* #__PURE__ */ (function () {
    return replacement !== highSurrogate;
})();
var outOfOrderSurrogates = /* #__PURE__ */ (function () {
    return lowSurrogate + highSurrogate === "\udf06\ud834";
})();
var hex = /* #__PURE__ */ (function () {
    return "\ud834\udf06\u2603\u03c6\xe0" === "\ud834\udf06\u2603\u03c6\xe0";
})();
var main = function __do() {
    Test_Assert["assert$prime"]("single-character escape sequences")(singleCharacter)();
    Test_Assert["assert$prime"]("hex escape sequences")(hex)();
    Test_Assert["assert$prime"]("astral code points are represented as a UTF-16 surrogate pair")(surrogatePair)();
    Test_Assert["assert$prime"]("lone surrogates may be combined into a surrogate pair")(loneSurrogates)();
    Test_Assert["assert$prime"]("lone surrogates may be combined out of order to remain lone surrogates")(outOfOrderSurrogates)();
    Test_Assert["assert$prime"]("lone surrogates are not replaced with the Unicode replacement character U+FFFD")(notReplacing)();
    return Effect_Console.log("Done")();
};
export {
    singleCharacter,
    hex,
    surrogatePair,
    highSurrogate,
    lowSurrogate,
    loneSurrogates,
    outOfOrderSurrogates,
    replacement,
    notReplacing,
    main
};
