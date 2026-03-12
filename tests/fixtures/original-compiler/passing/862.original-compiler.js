import * as Data_Functor from "../Data.Functor/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var id$prime = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorFn)(function (x) {
    return x;
})(function (y) {
    return y;
});
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ id$prime("Done"));
export {
    id$prime,
    main
};
