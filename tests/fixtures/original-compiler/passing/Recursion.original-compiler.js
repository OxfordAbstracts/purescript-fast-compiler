import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fib = function (n) {
    if (n === 0.0) {
        return 1.0;
    };
    if (n === 1.0) {
        return 1.0;
    };
    return fib(n - 1.0) + fib(n - 2.0);
};
export {
    fib,
    main
};
