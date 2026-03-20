import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var S = /* #__PURE__ */ (function () {
    function S(value0) {
        this.value0 = value0;
    };
    S.create = function (value0) {
        return new S(value0);
    };
    return S;
})();
var state = function (dict) {
    return dict.state;
};
var test2 = function (dictT) {
    return state(dictT)(function (o) {
        var $7 = {};
        for (var $8 in o) {
            if ({}.hasOwnProperty.call(o, $8)) {
                $7[$8] = o[$8];
            };
        };
        $7.foo = o.foo + "!";
        return $7;
    });
};
var st = {
    state: function (f) {
        return new S(function (s) {
            return {
                "new": f(s),
                ret: Data_Unit.unit
            };
        });
    }
};
var test1 = /* #__PURE__ */ state(st)(function (o) {
    var $10 = {};
    for (var $11 in o) {
        if ({}.hasOwnProperty.call(o, $11)) {
            $10[$11] = o[$11];
        };
    };
    $10.foo = o.foo + "!";
    return $10;
});
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    state,
    S,
    test1,
    test2,
    main,
    st
};
