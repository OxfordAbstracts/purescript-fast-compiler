import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foo = function (x) {
    if (x.foo === "Foo") {
        return x;
    };
    return x;
};
export {
    foo,
    main
};
