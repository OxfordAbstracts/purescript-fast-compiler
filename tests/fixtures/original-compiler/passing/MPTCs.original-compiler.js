import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var nullaryTypeClass = {
    greeting: "Hello, World!"
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var greeting = function (dict) {
    return dict.greeting;
};
var coerceShow = function (dictShow) {
    return {
        coerce: Data_Show.show(dictShow)
    };
};
var coerceRefl = {
    coerce: function (a) {
        return a;
    }
};
var coerce = function (dict) {
    return dict.coerce;
};
export {
    coerce,
    greeting,
    main,
    nullaryTypeClass,
    coerceShow,
    coerceRefl
};
