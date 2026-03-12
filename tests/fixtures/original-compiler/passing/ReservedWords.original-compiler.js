import * as Effect_Console from "../Effect.Console/index.js";
var o = {
    type: "o"
};
var p = {
    type: "p"
};
var f = function (v) {
    if (v.type === "p") {
        return "Done";
    };
    return "Fail";
};
var main = /* #__PURE__ */ (function () {
    return Effect_Console.log(f({
        type: p.type,
        foo: "bar"
    }));
})();
export {
    o,
    p,
    f,
    main
};
