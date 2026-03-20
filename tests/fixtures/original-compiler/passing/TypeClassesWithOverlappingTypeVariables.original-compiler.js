import * as Effect_Console from "../Effect.Console/index.js";
var Left = /* #__PURE__ */ (function () {
    function Left(value0) {
        this.value0 = value0;
    };
    Left.create = function (value0) {
        return new Left(value0);
    };
    return Left;
})();
var Right = /* #__PURE__ */ (function () {
    function Right(value0) {
        this.value0 = value0;
    };
    Right.create = function (value0) {
        return new Right(value0);
    };
    return Right;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var functorEither = {
    map: function (v) {
        return function (v1) {
            if (v1 instanceof Left) {
                return new Left(v1.value0);
            };
            if (v1 instanceof Right) {
                return new Right(v(v1.value0));
            };
            throw new Error("Failed pattern match at Main (line 8, column 1 - line 10, column 32): " + [ v.constructor.name, v1.constructor.name ]);
        };
    }
};
export {
    Left,
    Right,
    main,
    functorEither
};
