import * as $foreign from "./foreign.js";
import * as Effect_Console from "../Effect.Console/index.js";
var natPlusZ = {};
var natPlusS = function () {
    return {};
};
var natMultZ = {};
var natMultS = function () {
    return function () {
        return {};
    };
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
var fsingleton = function (x) {
    return $foreign.fcons(x)($foreign.fnil);
};
var fflatten = function () {
    return $foreign.fflattenImpl;
};
var fappend = function () {
    return $foreign.fappendImpl;
};
var fappend1 = /* #__PURE__ */ fappend();
var fexample = /* #__PURE__ */ fappend1(/* #__PURE__ */ fappend1(/* #__PURE__ */ $foreign.fcons(1)(/* #__PURE__ */ fsingleton(2)))(/* #__PURE__ */ fsingleton(3)))(/* #__PURE__ */ $foreign.fcons(4)(/* #__PURE__ */ fsingleton(5)));
var fexample2 = /* #__PURE__ */ fappend1(/* #__PURE__ */ fappend1(fexample)(fexample))(fexample);
var fexample3 = /* #__PURE__ */ fappend1(/* #__PURE__ */ fappend1(/* #__PURE__ */ fsingleton(fexample))(/* #__PURE__ */ fsingleton(fexample)))(/* #__PURE__ */ fsingleton(fexample));
var fexample4 = /* #__PURE__ */ fflatten()(fexample3);
export {
    fnil,
    fcons,
    fappendImpl,
    fflattenImpl,
    ftoArray
} from "./foreign.js";
export {
    fappend,
    fflatten,
    fsingleton,
    fexample,
    fexample2,
    fexample3,
    fexample4,
    main,
    natPlusZ,
    natPlusS,
    natMultZ,
    natMultS
};
