import * as Effect_Console from "../Effect.Console/index.js";
import * as ForeignKinds_Lib from "../ForeignKinds.Lib/index.js";
var proxy1Add2Is3 = /* #__PURE__ */ ForeignKinds_Lib.addNat()(ForeignKinds_Lib.proxy1)(ForeignKinds_Lib.proxy2);
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    proxy1Add2Is3,
    main
};
