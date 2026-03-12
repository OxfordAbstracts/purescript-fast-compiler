import * as Data_Newtype from "../Data.Newtype/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var wrap = /* #__PURE__ */ Data_Newtype.wrap();
var unwrap = /* #__PURE__ */ Data_Newtype.unwrap();
var Test = function (x) {
    return x;
};
var First = function (x) {
    return x;
};
var newtypeTest = {
    Coercible0: function () {
        return undefined;
    }
};
var t = /* #__PURE__ */ wrap("hello");
var newtypeFirst = {
    Coercible0: function () {
        return undefined;
    }
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var f = /* #__PURE__ */ wrap(1);
var i = /* #__PURE__ */ unwrap(f);
var a = /* #__PURE__ */ unwrap(t);
export {
    Test,
    t,
    a,
    First,
    f,
    i,
    main,
    newtypeTest,
    newtypeFirst
};
