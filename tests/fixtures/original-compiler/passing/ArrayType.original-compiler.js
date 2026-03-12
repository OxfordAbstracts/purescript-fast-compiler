import * as Effect_Console from "../Effect.Console/index.js";
var pointedArray = {
    point: function (a) {
        return [ a ];
    }
};
var point = function (dict) {
    return dict.point;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    point,
    main,
    pointedArray
};
