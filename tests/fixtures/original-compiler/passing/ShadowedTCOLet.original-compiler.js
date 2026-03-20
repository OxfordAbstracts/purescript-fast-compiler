import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var f = function (dictPartial) {
    return function (x) {
        return function (y) {
            return function (z) {
                var f2 = function (v) {
                    return function (v1) {
                        return function (v2) {
                            if (v === 1.0 && (v1 === 2.0 && v2 === 3.0)) {
                                return 1.0;
                            };
                            throw new Error("Failed pattern match at Main (line 9, column 7 - line 9, column 26): " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
                        };
                    };
                };
                return f2(x)(z)(y);
            };
        };
    };
};
var f1 = /* #__PURE__ */ f();
var main = function __do() {
    Effect_Console.log(Data_Show.show(Data_Show.showNumber)(f1(1.0)(3.0)(2.0)))();
    return Effect_Console.log("Done")();
};
export {
    f,
    main
};
