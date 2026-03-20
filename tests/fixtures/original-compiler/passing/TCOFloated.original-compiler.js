import * as Data_Ord from "../Data.Ord/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var lessThanOrEq = /* #__PURE__ */ Data_Ord.lessThanOrEq(/* #__PURE__ */ Data_Ord.ordRecord()(/* #__PURE__ */ Data_Ord.ordRecordCons(Data_Ord.ordRecordNil)()({
    reflectSymbol: function () {
        return "foo";
    }
})(Data_Ord.ordInt)));
var looper = function ($copy_x) {
    var $tco_done = false;
    var $tco_result;
    function $tco_loop(x) {
        var $9 = lessThanOrEq(x)({
            foo: 0
        });
        if ($9) {
            $tco_done = true;
            return "Done";
        };
        $copy_x = {
            foo: x.foo - 1 | 0
        };
        return;
    };
    while (!$tco_done) {
        $tco_result = $tco_loop($copy_x);
    };
    return $tco_result;
};
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ looper({
    foo: 100000
}));
export {
    main,
    looper
};
