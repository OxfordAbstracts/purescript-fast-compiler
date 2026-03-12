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
var Pure = /* #__PURE__ */ (function () {
    function Pure(value0) {
        this.value0 = value0;
    };
    Pure.create = function (value0) {
        return new Pure(value0);
    };
    return Pure;
})();
var Bind = /* #__PURE__ */ (function () {
    function Bind(value0) {
        this.value0 = value0;
    };
    Bind.create = function (value0) {
        return new Bind(value0);
    };
    return Bind;
})();
var TestA = /* #__PURE__ */ (function () {
    function TestA(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    TestA.create = function (value0) {
        return function (value1) {
            return new TestA(value0, value1);
        };
    };
    return TestA;
})();
var TestB = /* #__PURE__ */ (function () {
    function TestB(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    TestB.create = function (value0) {
        return function (value1) {
            return new TestB(value0, value1);
        };
    };
    return TestB;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var $lazy_hasOnly = /* #__PURE__ */ $runtime_lazy("hasOnly", "Main", function () {
    var go = function ($copy_v) {
        var $tco_done = false;
        var $tco_result;
        function $tco_loop(v) {
            if (v instanceof Pure) {
                $tco_done = true;
                return true;
            };
            if (v instanceof Bind && v.value0 instanceof TestA) {
                $copy_v = v.value0.value1;
                return;
            };
            if (v instanceof Bind && v.value0 instanceof TestB) {
                var $6 = $lazy_hasOnly(18)(v.value0.value0);
                if ($6) {
                    $copy_v = v.value0.value1;
                    return;
                };
                $tco_done = true;
                return false;
            };
            throw new Error("Failed pattern match at Main (line 15, column 5 - line 15, column 44): " + [ v.constructor.name ]);
        };
        while (!$tco_done) {
            $tco_result = $tco_loop($copy_v);
        };
        return $tco_result;
    };
    return go;
});
var hasOnly = /* #__PURE__ */ $lazy_hasOnly(12);
export {
    Pure,
    Bind,
    TestA,
    TestB,
    hasOnly,
    main
};
