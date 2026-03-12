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
var mapTree = function (v) {
    return function (v1) {
        if (v1 instanceof Leaf) {
            return new Leaf(v1.value0);
        };
        if (v1 instanceof Branch) {
            return new Branch(mapTree(v)(v1.value0), mapTree(v)(v1.value1));
        };
        throw new Error("Failed pattern match at Main (line 12, column 1 - line 12, column 62): " + [ v.constructor.name, v1.constructor.name ]);
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Leaf,
    Branch,
    mapTree,
    main
};
