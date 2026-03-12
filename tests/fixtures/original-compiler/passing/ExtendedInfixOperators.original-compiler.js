import * as Data_Function from "../Data.Function/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var $$null = function (v) {
    if (v.length === 0) {
        return true;
    };
    return false;
};
var comparing = function (dictOrd) {
    var compare = Data_Ord.compare(dictOrd);
    return function (f) {
        return Data_Function.on(compare)(f);
    };
};
var test = /* #__PURE__ */ comparing(Data_Ord.ordBoolean)($$null)([ 1.0, 2.0, 3.0 ])([ 4.0, 5.0, 6.0 ]);
var main = function __do() {
    Effect_Console.logShow(Data_Ordering.showOrdering)(test)();
    return Effect_Console.log("Done")();
};
export {
    comparing,
    $$null as null,
    test,
    main
};
