import * as Effect_Console from "../Effect.Console/index.js";
var Prim = /* #__PURE__ */ (function () {
    function Prim() {

    };
    Prim.value = new Prim();
    return Prim;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var f = function () {
    return function (v) {
        if (v === 0) {
            return 0;
        };
        throw new Error("Failed pattern match at Main (line 8, column 1 - line 8, column 27): " + [ v.constructor.name ]);
    };
};
var f1 = /* #__PURE__ */ f();
var f$prime = f1;
export {
    Prim,
    f,
    f$prime,
    main
};
