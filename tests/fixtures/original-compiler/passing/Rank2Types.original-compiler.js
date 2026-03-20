import * as Effect_Console from "../Effect.Console/index.js";
var test1 = function (f) {
    return f(0.0);
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var forever = function (bind) {
    return function (action) {
        return bind(action)(function (v) {
            return forever(bind)(action);
        });
    };
};
export {
    test1,
    forever,
    main
};
