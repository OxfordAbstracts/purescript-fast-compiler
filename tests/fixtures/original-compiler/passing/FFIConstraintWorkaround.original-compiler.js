import * as $foreign from "./foreign.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var showFFI = function (dictShow) {
    return $foreign.showImpl(Data_Show.show(dictShow));
};
var showFFI1 = /* #__PURE__ */ showFFI(Data_Show.showString);
var showFFI2 = /* #__PURE__ */ showFFI(/* #__PURE__ */ Data_Show.showRecord()()(/* #__PURE__ */ Data_Show.showRecordFieldsCons({
    reflectSymbol: function () {
        return "a";
    }
})(/* #__PURE__ */ Data_Show.showRecordFieldsCons({
    reflectSymbol: function () {
        return "b";
    }
})(/* #__PURE__ */ Data_Show.showRecordFieldsCons({
    reflectSymbol: function () {
        return "c";
    }
})(/* #__PURE__ */ Data_Show.showRecordFieldsConsNil({
    reflectSymbol: function () {
        return "e";
    }
})(Data_Show.showNumber))(Data_Show.showChar))(Data_Show.showBoolean))(Data_Show.showInt)));
var main = function __do() {
    Test_Assert["assert$prime"]("Showing Int is correct")(showFFI(Data_Show.showInt)(4) === "4")();
    Test_Assert["assert$prime"]("Showing String is correct")(showFFI1("string") === "\"string\"")();
    Test_Assert["assert$prime"]("Showing Record is correct")(showFFI2({
        a: 1,
        b: true,
        c: "d",
        e: 4.0
    }) === "{ a: 1, b: true, c: 'd', e: 4.0 }")();
    return Effect_Console.log("Done")();
};
export {
    showImpl
} from "./foreign.js";
export {
    main,
    showFFI
};
