import * as Control_Category from "../Control.Category/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var NonexportedType = /* #__PURE__ */ (function () {
    function NonexportedType() {

    };
    NonexportedType.value = new NonexportedType();
    return NonexportedType;
})();
var Const = /* #__PURE__ */ (function () {
    function Const(value0) {
        this.value0 = value0;
    };
    Const.create = function (value0) {
        return new Const(value0);
    };
    return Const;
})();
var notExported = function (dict) {
    return dict.notExported;
};
var nonExportedNonexportedType = /* #__PURE__ */ (function () {
    return {
        notExported: new Const(0)
    };
})();
var nonExportedFoo2 = function (dictNonexportedClass) {
    return {
        foo: notExported(dictNonexportedClass)
    };
};
var nonExportedFoo = function (dictFoo) {
    return {
        foo: identity
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var foo = function (dict) {
    return dict.foo;
};
var constFoo = /* #__PURE__ */ (function () {
    return {
        foo: new Const(NonexportedType.value)
    };
})();
export {
    Const,
    foo,
    main,
    nonExportedFoo,
    nonExportedFoo2
};
