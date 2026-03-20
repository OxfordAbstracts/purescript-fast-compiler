import * as Control_Category from "../Control.Category/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var F = function (x) {
    return x;
};
var unF = function (v) {
    return v;
};
var functorF = {
    map: function (f) {
        return function (m) {
            var $8 = {};
            for (var $9 in m) {
                if ({}.hasOwnProperty.call(m, $9)) {
                    $8[$9] = m[$9];
                };
            };
            $8.x = f(m.x);
            return $8;
        };
    }
};
var main = /* #__PURE__ */ (function () {
    return Effect_Console.log((unF(Data_Functor.map(functorF)(Control_Category.identity(Control_Category.categoryFn))({
        x: "Done",
        y: 42
    }))).x);
})();
export {
    F,
    unF,
    main,
    functorF
};
