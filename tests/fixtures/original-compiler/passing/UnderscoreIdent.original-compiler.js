import * as Effect_Console from "../Effect.Console/index.js";
var Con_Structor = /* #__PURE__ */ (function () {
    function Con_Structor() {

    };
    Con_Structor.value = new Con_Structor();
    return Con_Structor;
})();
var Con_2 = /* #__PURE__ */ (function () {
    function Con_2(value0) {
        this.value0 = value0;
    };
    Con_2.create = function (value0) {
        return new Con_2(value0);
    };
    return Con_2;
})();
var done = function (v) {
    if (v instanceof Con_2) {
        return v.value0;
    };
    return "Failed";
};
var main = /* #__PURE__ */ (function () {
    return Effect_Console.log(done(new Con_2("Done")));
})();
export {
    Con_Structor,
    Con_2,
    done,
    main
};
