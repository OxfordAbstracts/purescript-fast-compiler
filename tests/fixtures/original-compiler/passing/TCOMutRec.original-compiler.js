import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
import * as Test_Assert from "../Test.Assert/index.js";
var div = /* #__PURE__ */ Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt);
var assertEqual = /* #__PURE__ */ Test_Assert.assertEqual(Data_Eq.eqInt)(Data_Show.showInt);
var tco4 = /* #__PURE__ */ (function () {
    var f = function ($copy_x) {
        return function ($copy_y) {
            var $tco_var_x = $copy_x;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(x, y) {
                var g = function (y$prime) {
                    $tco_var_x = x + 2 | 0;
                    $copy_y = y$prime;
                    return;
                };
                var $15 = y <= 0;
                if ($15) {
                    $tco_done = true;
                    return x;
                };
                return g(y - 1 | 0);
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_x, $copy_y);
            };
            return $tco_result;
        };
    };
    return f(0);
})();
var tco3 = function (y0) {
    var j = function (x) {
        return x + 3 | 0;
    };
    var f = function ($copy_x) {
        return function ($copy_y) {
            var $tco_var_x = $copy_x;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(x, y) {
                var h = function (y1) {
                    return y1 - 1 | 0;
                };
                var g = function ($copy_x$prime) {
                    return function ($copy_y$prime) {
                        var $tco_var_x$prime = $copy_x$prime;
                        var $tco_done1 = false;
                        var $tco_result;
                        function $tco_loop(x$prime, y$prime) {
                            var $16 = y$prime <= 0;
                            if ($16) {
                                $tco_done = true;
                                $tco_done1 = true;
                                return x$prime;
                            };
                            var $17 = y$prime > div(y0)(2);
                            if ($17) {
                                $tco_var_x$prime = j(x$prime);
                                $copy_y$prime = y$prime - 1 | 0;
                                return;
                            };
                            $tco_var_x = x$prime + 2 | 0;
                            $copy_y = y$prime;
                            $tco_done1 = true;
                            return;
                        };
                        while (!$tco_done1) {
                            $tco_result = $tco_loop($tco_var_x$prime, $copy_y$prime);
                        };
                        return $tco_result;
                    };
                };
                return g(x)(h(y));
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_x, $copy_y);
            };
            return $tco_result;
        };
    };
    return f(0)(y0);
};
var tco2 = /* #__PURE__ */ (function () {
    var f = function ($copy_x) {
        return function ($copy_y) {
            var $tco_var_x = $copy_x;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(x, y) {
                var h = function (test) {
                    return function (x$prime) {
                        return function (y$prime) {
                            if (test) {
                                $tco_done = true;
                                return x$prime;
                            };
                            $tco_var_x = x$prime;
                            $copy_y = y$prime;
                            return;
                        };
                    };
                };
                var g = function (x$prime) {
                    return function (y$prime) {
                        return h(y$prime <= 0)(x$prime)(y$prime);
                    };
                };
                return g(x + 2 | 0)(y - 1 | 0);
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_x, $copy_y);
            };
            return $tco_result;
        };
    };
    return f(0);
})();
var tco1 = /* #__PURE__ */ (function () {
    var f = function ($copy_x) {
        return function ($copy_y) {
            var $tco_var_x = $copy_x;
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(x, y) {
                var g = function (x$prime) {
                    return function (y$prime) {
                        var $19 = y$prime <= 0;
                        if ($19) {
                            $tco_done = true;
                            return x$prime;
                        };
                        $tco_var_x = x$prime;
                        $copy_y = y$prime;
                        return;
                    };
                };
                return g(x + 2 | 0)(y - 1 | 0);
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($tco_var_x, $copy_y);
            };
            return $tco_result;
        };
    };
    return f(0);
})();
var ntco4 = /* #__PURE__ */ (function () {
    var f = function (x) {
        return function (y) {
            var h = function (x$prime) {
                return function (y$prime) {
                    return f(x$prime + 2 | 0)(y$prime);
                };
            };
            var g = h(x);
            var $20 = y <= 0;
            if ($20) {
                return x;
            };
            return g(y - 1 | 0);
        };
    };
    return f(0);
})();
var ntco3 = /* #__PURE__ */ (function () {
    var f = function (x) {
        return function (y) {
            var g = f(x + 2 | 0);
            var $21 = y <= 0;
            if ($21) {
                return x;
            };
            return g(y - 1 | 0);
        };
    };
    return f(0);
})();
var ntco2 = /* #__PURE__ */ (function () {
    var f = function (x) {
        return function (y) {
            var g = function (x$prime) {
                return f(x$prime + 2 | 0);
            };
            var $22 = y <= 0;
            if ($22) {
                return x;
            };
            return g(x)(y - 1 | 0);
        };
    };
    return f(0);
})();
var ntco1 = function (y0) {
    var f = function (x) {
        var g = function (x$prime) {
            return function (y$prime) {
                return f(x$prime + 10 | 0)(y$prime - 1 | 0);
            };
        };
        var $23 = x > (10 * y0 | 0);
        if ($23) {
            return function (v) {
                return x + v | 0;
            };
        };
        return g(x);
    };
    return f(0)(y0);
};
var main = function __do() {
    assertEqual({
        expected: 200000,
        actual: tco1(100000)
    })();
    assertEqual({
        expected: 200000,
        actual: tco2(100000)
    })();
    assertEqual({
        expected: 249997,
        actual: tco3(100000)
    })();
    assertEqual({
        expected: 200000,
        actual: tco4(100000)
    })();
    assertEqual({
        expected: 1009,
        actual: ntco1(100)
    })();
    Test_Assert.assertThrows(function (v) {
        return ntco1(100000);
    })();
    assertEqual({
        expected: 200,
        actual: ntco2(100)
    })();
    Test_Assert.assertThrows(function (v) {
        return ntco2(100000);
    })();
    assertEqual({
        expected: 200,
        actual: ntco3(100)
    })();
    Test_Assert.assertThrows(function (v) {
        return ntco3(100000);
    })();
    assertEqual({
        expected: 200,
        actual: ntco4(100)
    })();
    Test_Assert.assertThrows(function (v) {
        return ntco4(100000);
    })();
    return Effect_Console.log("Done")();
};
export {
    tco1,
    tco2,
    tco3,
    tco4,
    ntco1,
    ntco2,
    ntco3,
    ntco4,
    main
};
