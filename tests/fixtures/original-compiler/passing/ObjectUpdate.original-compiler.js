import * as Effect_Console from "../Effect.Console/index.js";
var update2 = function (o) {
    var $8 = {};
    for (var $9 in o) {
        if ({}.hasOwnProperty.call(o, $9)) {
            $8[$9] = o[$9];
        };
    };
    $8.foo = "Foo";
    return $8;
};
var update1 = function (o) {
    var $11 = {};
    for (var $12 in o) {
        if ({}.hasOwnProperty.call(o, $12)) {
            $11[$12] = o[$12];
        };
    };
    $11.foo = "Foo";
    return $11;
};
var replace = function (o) {
    if (o.foo === "Foo") {
        var $15 = {};
        for (var $16 in o) {
            if ({}.hasOwnProperty.call(o, $16)) {
                $15[$16] = o[$16];
            };
        };
        $15.foo = "Bar";
        return $15;
    };
    if (o.foo === "Bar") {
        var $19 = {};
        for (var $20 in o) {
            if ({}.hasOwnProperty.call(o, $20)) {
                $19[$20] = o[$20];
            };
        };
        $19.bar = "Baz";
        return $19;
    };
    return o;
};
var polyUpdate = function (o) {
    var $23 = {};
    for (var $24 in o) {
        if ({}.hasOwnProperty.call(o, $24)) {
            $23[$24] = o[$24];
        };
    };
    $23.foo = "Foo";
    return $23;
};
var main = function __do() {
    Effect_Console.log((update1({
        foo: ""
    })).foo)();
    return Effect_Console.log("Done")();
};
var inferPolyUpdate = function (o) {
    var $26 = {};
    for (var $27 in o) {
        if ({}.hasOwnProperty.call(o, $27)) {
            $26[$27] = o[$27];
        };
    };
    $26.foo = "Foo";
    return $26;
};
export {
    update1,
    update2,
    replace,
    polyUpdate,
    inferPolyUpdate,
    main
};
