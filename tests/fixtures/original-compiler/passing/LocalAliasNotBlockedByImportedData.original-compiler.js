import * as Effect_Console from "../Effect.Console/index.js";
var update = function (m) {
    return m.name;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var getPage = function (m) {
    return m.page;
};
var getName = function (m) {
    return m.name;
};
var getCount = function (m) {
    return m.count;
};
export {
    update,
    getName,
    getCount,
    getPage,
    main
};
