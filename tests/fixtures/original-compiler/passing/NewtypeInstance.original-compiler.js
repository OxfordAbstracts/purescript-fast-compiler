import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Tuple from "../Data.Tuple/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var Y = function (x) {
    return x;
};
var ProxyArray = function (x) {
    return x;
};
var Proxy2 = /* #__PURE__ */ (function () {
    function Proxy2() {

    };
    Proxy2.value = new Proxy2();
    return Proxy2;
})();
var MyWriter = function (x) {
    return x;
};
var X = function (x) {
    return x;
};
var MyArray = function (x) {
    return x;
};
var Syn = function (x) {
    return x;
};
var Foo = function (x) {
    return x;
};
var functorProxy2 = {
    map: function (f) {
        return function (m) {
            return Proxy2.value;
        };
    }
};
var functorFoo = functorProxy2;
var tell = function (dict) {
    return dict.tell;
};
var singletonArray = {
    singleton: function (x) {
        return [ x ];
    }
};
var singletonY = singletonArray;
var singleton = function (dict) {
    return dict.singleton;
};
var singleton1 = /* #__PURE__ */ singleton(singletonY);
var showY = /* #__PURE__ */ Data_Show.showArray(Data_Show.showString);
var logShow = /* #__PURE__ */ Effect_Console.logShow(showY);
var showX = Data_Show.showString;
var showMyArray = function (dictShow) {
    return Data_Show.showArray(dictShow);
};
var logShow1 = /* #__PURE__ */ Effect_Console.logShow(/* #__PURE__ */ showMyArray(Data_Show.showString));
var ordX = Data_Ord.ordString;
var monadWriterTuple = function (dictMonoid) {
    var monadTuple = Data_Tuple.monadTuple(dictMonoid);
    return {
        tell: function (w) {
            return new Data_Tuple.Tuple(w, Data_Unit.unit);
        },
        Monad0: function () {
            return monadTuple;
        },
        Monoid1: function () {
            return dictMonoid;
        }
    };
};
var monadWriterMyWriter = function (dictMonoid) {
    return monadWriterTuple(dictMonoid);
};
var monadMyWriter = function (dictMonoid) {
    return Data_Tuple.monadTuple(dictMonoid);
};
var functorProxyArray = Data_Functor.functorArray;
var functorMyWriter = Data_Tuple.functorTuple;
var functorSyn = functorMyWriter;
var functorMyArray = Data_Functor.functorArray;
var map = /* #__PURE__ */ Data_Functor.map(functorMyArray);
var main = function __do() {
    Effect_Console.logShow(showX)("test")();
    logShow(singleton1("test"))();
    logShow1(map(show)([ 1, 2, 3 ]))();
    return Effect_Console.log("Done")();
};
var eqX = Data_Eq.eqString;
var bindMyWriter = function (dictSemigroup) {
    return Data_Tuple.bindTuple(dictSemigroup);
};
var applyMyWriter = function (dictSemigroup) {
    return Data_Tuple.applyTuple(dictSemigroup);
};
var applicativeMyWriter = function (dictMonoid) {
    return Data_Tuple.applicativeTuple(dictMonoid);
};
export {
    singleton,
    tell,
    X,
    Y,
    MyArray,
    ProxyArray,
    MyWriter,
    Syn,
    Proxy2,
    Foo,
    main,
    showX,
    eqX,
    ordX,
    showY,
    singletonArray,
    singletonY,
    showMyArray,
    functorMyArray,
    functorProxyArray,
    monadWriterTuple,
    functorMyWriter,
    applyMyWriter,
    applicativeMyWriter,
    bindMyWriter,
    monadMyWriter,
    monadWriterMyWriter,
    functorSyn,
    functorProxy2,
    functorFoo
};
