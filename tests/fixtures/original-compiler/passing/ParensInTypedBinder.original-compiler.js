import * as Control_Bind from "../Control.Bind/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var bind = /* #__PURE__ */ Control_Bind.bind(Control_Bind.bindArray);
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foo = /* #__PURE__ */ bind([ [ [ 1, 2, 3 ], [ 4, 5 ] ], [ [ 6 ] ] ])(function (v) {
    return bind(v)(function (v1) {
        return v1;
    });
});
export {
    foo,
    main
};
