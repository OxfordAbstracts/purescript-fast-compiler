import * as Data_Reflectable from "../Data.Reflectable/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Type_Proxy from "../Type.Proxy/index.js";
var reflect = function (dictReflectable) {
    return Data_Reflectable.reflectType(dictReflectable)(Type_Proxy["Proxy"].value);
};
var use = /* #__PURE__ */ Data_Show.show(/* #__PURE__ */ Data_Show.showRecord()()(/* #__PURE__ */ Data_Show.showRecordFieldsConsNil({
    reflectSymbol: function () {
        return "asdf";
    }
})(Data_Show.showString)))({
    asdf: /* #__PURE__ */ reflect({
        reflectType: function () {
            return "asdf";
        }
    })
});
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    reflect,
    use,
    main
};
