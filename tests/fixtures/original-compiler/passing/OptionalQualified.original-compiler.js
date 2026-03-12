import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var bind = Control_Bind.bind;
var main = /* #__PURE__ */ bind(Effect.bindEffect)(/* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect)("Done"))(function (message) {
    return Effect_Console.log(message);
});
export {
    bind,
    main
};
