import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var test2 = {
    showP: function (v) {
        return "Symbol";
    }
};
var test1 = {
    showP: function (v) {
        return "Type";
    }
};
var showP = function (dict) {
    return dict.showP;
};
var showP1 = /* #__PURE__ */ showP(test2);
var main = function __do() {
    Test_Assert.assert(showP(test1)($$Proxy.value) === "Type")();
    Test_Assert.assert(showP1($$Proxy.value) === "Symbol")();
    return Effect_Console.log("Done")();
};
export {
    showP,
    $$Proxy as Proxy,
    main,
    test1,
    test2
};
