import * as Effect_Console from "../Effect.Console/index.js";
var Leaf = /* #__PURE__ */ (function () {
    function Leaf(value0) {
        this.value0 = value0;
    };
    Leaf.create = function (value0) {
        return new Leaf(value0);
    };
    return Leaf;
})();
var Branch = /* #__PURE__ */ (function () {
    function Branch(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Branch.create = function (value0) {
        return function (value1) {
            return new Branch(value0, value1);
        };
    };
    return Branch;
})();
var constClass1 = {
    constClass: function (a) {
        return function (v) {
            return a;
        };
    }
};
var treeInt$prime = /* #__PURE__ */ (function () {
    return Branch.create;
})();
var treeInt = /* #__PURE__ */ (function () {
    return Leaf.create;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var identityCheck = 0;
var identityPass = identityCheck;
var constClass = function (dict) {
    return dict.constClass;
};
var constClassInt = /* #__PURE__ */ constClass(constClass1);
var constCheck = 0;
var constPass = constCheck;
export {
    constClass,
    identityCheck,
    identityPass,
    constCheck,
    constPass,
    constClassInt,
    Leaf,
    Branch,
    treeInt,
    treeInt$prime,
    main,
    constClass1
};
