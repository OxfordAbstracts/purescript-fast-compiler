import * as Effect_Console from "../Effect.Console/index.js";
var UpdateDto = function (x) {
    return x;
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var eqUpdateDto = {
    eq: function (x) {
        return function (y) {
            return x.bio === y.bio;
        };
    }
};
export {
    UpdateDto,
    main,
    eqUpdateDto
};
