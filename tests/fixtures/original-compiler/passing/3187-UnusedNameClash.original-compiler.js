import * as Effect_Console from "../Effect.Console/index.js";
var abuseUnused = function (__unused) {
    return __unused;
};
var main = /* #__PURE__ */ (function () {
    var explode = abuseUnused(0) + abuseUnused(0) | 0;
    return Effect_Console.log("Done");
})();
export {
    main
};
