import * as Effect_Console from "../Effect.Console/index.js";
var test = function (x) {
    if (x.str === "Foo" && x.bool) {
        return true;
    };
    if (x.str === "Bar") {
        return x.bool;
    };
    return false;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var isDesc = function (v) {
    if (v.length === 2 && v[0] > v[1]) {
        return true;
    };
    return false;
};
var h = function (o) {
    if (o.length === 3) {
        return o;
    };
    return [  ];
};
var f = function (o) {
    if (o.foo === "Foo") {
        return o.bar;
    };
    return 0;
};
export {
    test,
    f,
    h,
    isDesc,
    main
};
