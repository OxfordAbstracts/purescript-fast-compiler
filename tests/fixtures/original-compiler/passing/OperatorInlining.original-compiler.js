import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var logShow = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showNumber);
var logShow1 = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showBoolean);
var logShow2 = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showString);
var main = function __do() {
    logShow(1.0 + 2.0)();
    logShow(1.0 * 2.0)();
    logShow(1.0 - 2.0)();
    logShow(-1.0)();
    logShow(1.0 / 2.0)();
    logShow1(1.0 > 2.0)();
    logShow1(1.0 < 2.0)();
    logShow1(1.0 <= 2.0)();
    logShow1(1.0 >= 2.0)();
    logShow1(1.0 === 2.0)();
    logShow1(1.0 === 2.0)();
    logShow1(1.0 !== 2.0)();
    logShow1("foo" === "bar")();
    logShow1("foo" !== "bar")();
    logShow1(true === false)();
    logShow1(true !== false)();
    logShow2("foo" + "bar")();
    logShow1(true && true)();
    logShow1(false || false)();
    logShow1(!true)();
    return Effect_Console.log("Done")();
};
export {
    main
};
