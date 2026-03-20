import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var Person = /* #__PURE__ */ (function () {
    function Person(value0) {
        this.value0 = value0;
    };
    Person.create = function (value0) {
        return new Person(value0);
    };
    return Person;
})();
var showPerson = function (p) {
    return p.value0.name + (", aged " + show(p.value0.age));
};
var main = /* #__PURE__ */ Effect_Console.log("Done");
export {
    Person,
    showPerson,
    main
};
