import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var g = function (v) {
    return v(function (y) {
        return y;
    });
};
var test2 = /* #__PURE__ */ g(function (f1) {
    var $3 = f1(true);
    if ($3) {
        return f1(0);
    };
    return f1(1);
});
var f = function (v) {
    return v(v);
};
var test1 = /* #__PURE__ */ f(function (x) {
    return x;
})(1);
export {
    f,
    test1,
    g,
    test2,
    main
};
