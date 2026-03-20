import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var test = function ($copy_v) {
    var $tco_done = false;
    var $tco_result;
    function $tco_loop(v) {
        if (v === 100) {
            $tco_done = true;
            return 100;
        };
        $copy_v = 1 + v | 0;
        return;
    };
    while (!$tco_done) {
        $tco_result = $tco_loop($copy_v);
    };
    return $tco_result;
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showInt)(test(0))();
    return Effect_Console.log("Done")();
};
export {
    test,
    main
};
