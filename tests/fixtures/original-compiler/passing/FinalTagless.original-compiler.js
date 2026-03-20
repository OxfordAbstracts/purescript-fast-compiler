import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var Id = /* #__PURE__ */ (function () {
    function Id(value0) {
        this.value0 = value0;
    };
    Id.create = function (value0) {
        return new Id(value0);
    };
    return Id;
})();
var runId = function (v) {
    return v.value0;
};
var num = function (dict) {
    return dict.num;
};
var exprId = /* #__PURE__ */ (function () {
    return {
        num: Id.create,
        add: function (v) {
            return function (v1) {
                return new Id(v.value0 + v1.value0);
            };
        }
    };
})();
var add = function (dict) {
    return dict.add;
};
var three = function (dictE) {
    var num1 = num(dictE);
    return add(dictE)(num1(1.0))(num1(2.0));
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showNumber)(runId(three(exprId)))();
    return Effect_Console.log("Done")();
};
export {
    add,
    num,
    Id,
    runId,
    three,
    main,
    exprId
};
