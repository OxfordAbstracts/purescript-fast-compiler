import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var Check = /* #__PURE__ */ (function () {
    function Check() {

    };
    Check.value = new Check();
    return Check;
})();
var withArgHasEmptySuper = function (dict) {
    return dict.withArgHasEmptySuper;
};
var withArgEmptyCheck = {};
var withArgHasEmptySuperCheck = /* #__PURE__ */ (function () {
    return {
        withArgHasEmptySuper: Check.value,
        WithArgEmpty0: function () {
            return undefined;
        }
    };
})();
var whenAccessingSuperDict = /* #__PURE__ */ (function () {
    var bar = function () {
        return function (x) {
            return x;
        };
    };
    var bar1 = bar();
    var foo = function (dictWithArgHasEmptySuper) {
        return function (x) {
            return bar1(x);
        };
    };
    return foo(withArgHasEmptySuperCheck)(Check.value);
})();
var hasNonEmptySuperInst = function (dictHasEmptySuper) {
    return {
        HasEmptySuper0: function () {
            return dictHasEmptySuper;
        }
    };
};
var hasEmptySuper = function (dict) {
    return dict.hasEmptySuper;
};
var eqCheck = {
    eq: function (x) {
        return function (y) {
            return true;
        };
    }
};
var eq = /* #__PURE__ */ Data_Eq.eq(eqCheck);
var emptyDictInst = {};
var hasEmptySuperInst = /* #__PURE__ */ (function () {
    return {
        hasEmptySuper: Check.value,
        EmptyClass0: function () {
            return undefined;
        }
    };
})();
var whenHasEmptySuper = /* #__PURE__ */ (function (dictHasEmptySuper) {
    return Check.value;
})(hasEmptySuperInst);
var whenHasNonEmptySuper = /* #__PURE__ */ (function (dictHasNonEmptySuper) {
    return Check.value;
})(/* #__PURE__ */ hasNonEmptySuperInst(hasEmptySuperInst));
var whenEmpty = /* #__PURE__ */ (function () {
    return Check.value;
})();
var aliasEmptyClassInst = {
    EmptyClass0: function () {
        return undefined;
    }
};
var whenAliasEmptyClass = /* #__PURE__ */ (function () {
    return Check.value;
})();
var main = /* #__PURE__ */ (function () {
    var $16 = eq(Check.value)(whenEmpty) && (eq(Check.value)(whenHasEmptySuper) && (eq(Check.value)(whenHasNonEmptySuper) && (eq(Check.value)(whenAliasEmptyClass) && eq(Check.value)(whenAccessingSuperDict))));
    if ($16) {
        return Effect_Console.log("Done");
    };
    return Control_Applicative.pure(Effect.applicativeEffect)(Data_Unit.unit);
})();
export {
    hasEmptySuper,
    withArgHasEmptySuper,
    Check,
    whenEmpty,
    whenHasEmptySuper,
    whenHasNonEmptySuper,
    whenAliasEmptyClass,
    whenAccessingSuperDict,
    main,
    eqCheck,
    emptyDictInst,
    hasEmptySuperInst,
    hasNonEmptySuperInst,
    aliasEmptyClassInst,
    withArgEmptyCheck,
    withArgHasEmptySuperCheck
};
