import * as Data_Unit_1 from "../Data.Unit/index.js";
import * as Effect_Console_1 from "../Effect.Console/index.js";
var Effect_Console = /* #__PURE__ */ (function () {
    function Effect_Console() {

    };
    Effect_Console.value = new Effect_Console();
    return Effect_Console;
})();
var Data_Unit = function (x) {
    return x;
};
var n = Data_Unit_1.unit;
var main = /* #__PURE__ */ Effect_Console_1.log("Done");
var d = /* #__PURE__ */ (function () {
    return Effect_Console.value;
})();
export {
    Effect_Console,
    d,
    Data_Unit,
    n,
    main
};
