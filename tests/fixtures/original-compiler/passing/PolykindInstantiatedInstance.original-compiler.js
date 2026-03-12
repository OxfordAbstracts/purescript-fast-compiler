import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fProxy = {
    f: function (v) {
        return function (v1) {
            return $$Proxy.value;
        };
    }
};
var f = function (dict) {
    return dict.f;
};
var f1 = /* #__PURE__ */ f(fProxy);
var test1 = /* #__PURE__ */ (function () {
    return f1(function (a) {
        return a;
    })($$Proxy.value);
})();
var test2 = /* #__PURE__ */ (function () {
    return f1(function (a) {
        return a;
    })($$Proxy.value);
})();
var test3 = /* #__PURE__ */ (function () {
    return f1(function (a) {
        return "foo";
    })($$Proxy.value);
})();
export {
    f,
    $$Proxy as Proxy,
    test1,
    test2,
    test3,
    main,
    fProxy
};
