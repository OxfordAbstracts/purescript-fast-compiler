import * as Effect_Console from "../Effect.Console/index.js";
var main = /* #__PURE__ */ (function () {
    return Effect_Console.log(((function () {
        var v = {
            hasOwnProperty: "Hi"
        };
        return {
            hasOwnProperty: "Done"
        };
    })()).hasOwnProperty);
})();
export {
    main
};
