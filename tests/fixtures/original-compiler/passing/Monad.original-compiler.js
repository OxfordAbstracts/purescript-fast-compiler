import * as Effect_Console from "../Effect.Console/index.js";
var Nothing = /* #__PURE__ */ (function () {
    function Nothing() {

    };
    Nothing.value = new Nothing();
    return Nothing;
})();
var Just = /* #__PURE__ */ (function () {
    function Just(value0) {
        this.value0 = value0;
    };
    Just.create = function (value0) {
        return new Just(value0);
    };
    return Just;
})();
var Id = /* #__PURE__ */ (function () {
    function Id(value0) {
        this.value0 = value0;
    };
    Id.create = function (value0) {
        return new Id(value0);
    };
    return Id;
})();
var test = function (m) {
    return m.bind(m["return"](1.0))(function (n1) {
        return m.bind(m["return"]("Test"))(function (n2) {
            return m["return"](n1);
        });
    });
};
var maybe = /* #__PURE__ */ (function () {
    return {
        "return": Just.create,
        bind: function (ma) {
            return function (f) {
                if (ma instanceof Nothing) {
                    return Nothing.value;
                };
                if (ma instanceof Just) {
                    return f(ma.value0);
                };
                throw new Error("Failed pattern match at Main (line 18, column 21 - line 20, column 20): " + [ ma.constructor.name ]);
            };
        }
    };
})();
var test2 = /* #__PURE__ */ test(maybe);
var main = /* #__PURE__ */ Effect_Console.log("Done");
var id = /* #__PURE__ */ (function () {
    return {
        "return": Id.create,
        bind: function (ma) {
            return function (f) {
                return f(ma.value0);
            };
        }
    };
})();
var test1 = /* #__PURE__ */ test(id);
export {
    Id,
    id,
    Nothing,
    Just,
    maybe,
    test,
    test1,
    test2,
    main
};
