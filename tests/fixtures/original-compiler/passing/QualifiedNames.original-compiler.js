import * as Control_Category from "../Control.Category/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Either from "../Either/index.js";
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var either = function (v) {
    return function (v1) {
        return function (v2) {
            if (v2 instanceof Either.Left) {
                return v(v2.value0);
            };
            if (v2 instanceof Either.Right) {
                return v1(v2.value0);
            };
            throw new Error("Failed pattern match at Main (line 7, column 1 - line 7, column 71): " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
        };
    };
};
var main = /* #__PURE__ */ (function () {
    return Effect_Console.log(either(identity)(identity)(new Either.Left("Done")));
})();
export {
    either,
    main
};
