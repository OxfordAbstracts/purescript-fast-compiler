import * as Effect_Console from "../Effect.Console/index.js";
var greet = function (v) {
    return Effect_Console.log(v.greeting + (", " + (v.name + ".")));
};
var main = function __do() {
    greet({
        greeting: "Hello",
        name: "World"
    })();
    return Effect_Console.log("Done")();
};
export {
    greet,
    main
};
