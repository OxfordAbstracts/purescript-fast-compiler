import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var showString = {
    id: function (x) {
        return x;
    },
    Show0: function () {
        return Data_Show.showString;
    }
};
var id = function (dict) {
    return dict.id;
};
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ id(showString)("Done"));
export {
    id,
    main,
    showString
};
