import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var Box = /* #__PURE__ */ (function () {
    function Box(value0) {
        this.value0 = value0;
    };
    Box.create = function (value0) {
        return new Box(value0);
    };
    return Box;
})();
var strangeThing = function (dictSemigroup) {
    var append1 = Data_Semigroup.append(dictSemigroup);
    return function (x) {
        return function (y) {
            return append1(x)(y);
        };
    };
};
var showBox = function (dictShow) {
    var show = Data_Show.show(dictShow);
    return {
        show: function (v) {
            return "Box " + show(v.value0);
        }
    };
};
var method = function (dict) {
    return dict.method;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    method,
    Box,
    strangeThing,
    main,
    showBox
};
