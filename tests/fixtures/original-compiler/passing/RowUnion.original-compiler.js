import * as $foreign from "./foreign.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var logShow = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showInt);
var logShow1 = /* #__PURE__ */ Effect_Console.logShow(Data_Show.showBoolean);
var $$Proxy = /* #__PURE__ */ (function () {
    function $$Proxy() {

    };
    $$Proxy.value = new $$Proxy();
    return $$Proxy;
})();
var subrow = function () {
    return {};
};
var solve = function () {
    return function (v) {
        return function (v1) {
            return $$Proxy.value;
        };
    };
};
var solve1 = /* #__PURE__ */ solve();
var solveUnionBackwardsCons = /* #__PURE__ */ (function () {
    return solve1($$Proxy.value)($$Proxy.value);
})();
var solveUnionBackwardsDblCons = /* #__PURE__ */ (function () {
    return solve1($$Proxy.value)($$Proxy.value);
})();
var solveUnionBackwardsNil = /* #__PURE__ */ (function () {
    return solve1($$Proxy.value)($$Proxy.value);
})();
var merge = function () {
    return $foreign.mergeImpl;
};
var merge1 = /* #__PURE__ */ merge();
var mergeWithExtras = function () {
    return merge1;
};
var mergeWithExtras1 = /* #__PURE__ */ mergeWithExtras();
var test1 = /* #__PURE__ */ merge1({
    x: 1
})({
    y: true
});
var test2 = /* #__PURE__ */ merge1({
    x: 1
})({
    x: true
});
var test3 = function (x) {
    return merge1({
        x: 1
    })(x);
};
var test3$prime = function (dictUnion) {
    var merge2 = merge(dictUnion);
    return function (x) {
        return merge2(x)({
            x: 1
        });
    };
};
var withDefaults = function () {
    return function (p) {
        return merge1(p)({
            y: 1,
            z: 1
        });
    };
};
var withDefaults1 = /* #__PURE__ */ withDefaults();
var test4 = /* #__PURE__ */ withDefaults1({
    x: 1,
    y: 2
});
var withDefaultsClosed = function () {
    return function () {
        return function (p) {
            return merge1(p)({
                y: 1,
                z: 1
            });
        };
    };
};
var withDefaultsClosed1 = /* #__PURE__ */ withDefaultsClosed()();
var main = function __do() {
    logShow(test1.x)();
    logShow1(test1.y)();
    logShow1(test1.x === 1)();
    logShow((mergeWithExtras1({
        x: 1
    })({
        x: 0,
        y: true,
        z: 42.0
    })).x)();
    logShow((withDefaults1({
        x: 1
    })).x)();
    logShow((withDefaults1({
        x: 1
    })).y)();
    logShow((withDefaults1({
        x: 1
    })).z)();
    logShow((withDefaults1({
        x: 1,
        y: 2
    })).x)();
    logShow((withDefaults1({
        x: 1,
        y: 2
    })).y)();
    logShow((withDefaults1({
        x: 1,
        y: 2
    })).z)();
    logShow((withDefaultsClosed1({
        x: 1,
        y: 2
    })).x)();
    logShow((withDefaultsClosed1({
        x: 1,
        y: 2
    })).y)();
    logShow((withDefaultsClosed1({
        x: 1,
        y: 2
    })).z)();
    return Effect_Console.log("Done")();
};
export {
    mergeImpl
} from "./foreign.js";
export {
    $$Proxy as Proxy,
    solve,
    solveUnionBackwardsNil,
    solveUnionBackwardsCons,
    solveUnionBackwardsDblCons,
    merge,
    test1,
    test2,
    mergeWithExtras,
    test3,
    test3$prime,
    withDefaults,
    withDefaultsClosed,
    test4,
    main,
    subrow
};
