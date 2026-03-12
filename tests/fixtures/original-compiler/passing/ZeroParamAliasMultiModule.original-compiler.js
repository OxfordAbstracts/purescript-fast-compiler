import * as Consumer from "../Consumer/index.js";
import * as Data from "../Data/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var make = /* #__PURE__ */ (function () {
    return new Data.A(42, "hello");
})();
var test = /* #__PURE__ */ Consumer.consume(make);
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    make,
    test,
    main
};
