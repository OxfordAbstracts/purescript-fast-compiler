import * as Effect_Console from "../Effect.Console/index.js";
var ListT = /* #__PURE__ */ (function () {
    function ListT(value0) {
        this.value0 = value0;
    };
    ListT.create = function (value0) {
        return new ListT(value0);
    };
    return ListT;
})();
var myTransListT = /* #__PURE__ */ (function () {
    return {
        lift: ListT.create
    };
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    ListT,
    main,
    myTransListT
};
