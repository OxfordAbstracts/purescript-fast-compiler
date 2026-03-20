import * as Effect_Console from "../Effect.Console/index.js";
var fn = function (v) {
    return v.b.c.d;
};
var a = {
    b: {
        c: {
            d: 2
        }
    }
};
var d = /* #__PURE__ */ (function () {
    return fn(a) + a.b.c.d | 0;
})();
var main = /* #__PURE__ */ (function () {
    var $3 = (fn(a) + a.b.c.d | 0) === 4;
    if ($3) {
        return Effect_Console.log("Done");
    };
    return Effect_Console.log("Fail");
})();
export {
    fn,
    a,
    d,
    main
};
