import * as Effect_Console from "../Effect.Console/index.js";
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var test5 = {
    a: "test"
};
var test4 = [ "test" ];
var test3 = /* #__PURE__ */ (function () {
    return $$Proxy.value;
})();
var test1 = [ "test" ];
var main = /* #__PURE__ */ Effect_Console.log("Done");
var f = function (s) {
    return s;
};
var test2 = /* #__PURE__ */ f("test");
var def = function (dict) {
    return dict.def;
};
var clazzString = {
    def: "test"
};
export {
    def,
    test1,
    f,
    test2,
    $$Proxy as Proxy,
    test3,
    test4,
    test5,
    main,
    clazzString
};
