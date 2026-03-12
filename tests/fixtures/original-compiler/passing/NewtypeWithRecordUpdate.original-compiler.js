import * as Effect_Console from "../Effect.Console/index.js";
var NewType = function (x) {
    return x;
};
var rec1 = {
    a: 0.0,
    b: 0.0,
    c: 0.0
};
var rec2 = /* #__PURE__ */ (function () {
    return {
        b: rec1.b,
        c: rec1.c,
        a: 1.0
    };
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    NewType,
    rec1,
    rec2,
    main
};
