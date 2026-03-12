import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var ArrayBox = /* #__PURE__ */ (function () {
    function ArrayBox(value0) {
        this.value0 = value0;
    };
    ArrayBox.create = function (value0) {
        return new ArrayBox(value0);
    };
    return ArrayBox;
})();
var nil = /* #__PURE__ */ (function () {
    return new ArrayBox([  ]);
})();
var cons$prime = function (x) {
    return function (v) {
        return new ArrayBox(append([ x ])(v.value0));
    };
};
var main = /* #__PURE__ */ (function () {
    var v = cons$prime(1)(cons$prime(2)(cons$prime(3)(nil)));
    if (v.value0.length === 3 && (v["value0"][0] === 1 && (v["value0"][1] === 2 && v["value0"][2] === 3))) {
        return Effect_Console.log("Done");
    };
    return Test_Assert["assert$prime"]("Failed")(false);
})();
export {
    ArrayBox,
    nil,
    cons$prime,
    main
};
