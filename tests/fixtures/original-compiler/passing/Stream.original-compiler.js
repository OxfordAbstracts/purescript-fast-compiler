import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var $runtime_lazy = function (name, moduleName, init) {
    var state = 0;
    var val;
    return function (lineNumber) {
        if (state === 2) return val;
        if (state === 1) throw new ReferenceError(name + " was needed before it finished initializing (module " + moduleName + ", line " + lineNumber + ")", moduleName, lineNumber);
        state = 1;
        val = init();
        state = 2;
        return val;
    };
};
var Stream = /* #__PURE__ */ (function () {
    function Stream(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Stream.create = function (value0) {
        return function (value1) {
            return new Stream(value0, value1);
        };
    };
    return Stream;
})();
var uncons = function (dict) {
    return dict.uncons;
};
var streamIsStream = {
    cons: function (x) {
        return function (xs) {
            return new Stream(x, xs);
        };
    },
    uncons: function (v) {
        return {
            head: v.value0,
            tail: v.value1(Data_Unit.unit)
        };
    }
};
var cons = function (dict) {
    return dict.cons;
};
var test = function (dictIsStream) {
    var uncons1 = uncons(dictIsStream);
    var cons1 = cons(dictIsStream);
    return function (s) {
        var v = uncons1(s);
        return cons1(v.head)(function (v1) {
            return v.tail;
        });
    };
};
var main = /* #__PURE__ */ (function () {
    var $lazy_dones = $runtime_lazy("dones", "Main", function () {
        return cons(streamIsStream)("Done")(function (v) {
            return $lazy_dones(25);
        });
    });
    var dones = $lazy_dones(24);
    return Effect_Console.log((uncons(streamIsStream)(test(streamIsStream)(dones))).head);
})();
export {
    cons,
    uncons,
    Stream,
    test,
    main,
    streamIsStream
};
