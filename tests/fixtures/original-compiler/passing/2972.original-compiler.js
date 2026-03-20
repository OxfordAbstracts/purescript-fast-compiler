import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var Id = function (x) {
    return x;
};
var foo = function (dictShow) {
    return {
        show: function (v) {
            return "Done";
        }
    };
};
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ Data_Show.show(/* #__PURE__ */ foo(Data_Show.showString))("other"));
export {
    Id,
    main,
    foo
};
