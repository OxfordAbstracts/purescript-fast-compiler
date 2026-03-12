import * as Effect_Console from "../Effect.Console/index.js";
var Person = /* #__PURE__ */ (function () {
    function Person(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Person.create = function (value0) {
        return function (value1) {
            return new Person(value0, value1);
        };
    };
    return Person;
})();
var main = /* #__PURE__ */ Effect_Console.log("Done");
var getName = function (p) {
    if (p.value1) {
        return p.value0;
    };
    return "Unknown";
};
var name = /* #__PURE__ */ (function () {
    return getName(new Person("John Smith", true));
})();
export {
    Person,
    getName,
    name,
    main
};
