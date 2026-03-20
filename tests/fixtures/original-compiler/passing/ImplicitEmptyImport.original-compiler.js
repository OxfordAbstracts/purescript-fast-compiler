import * as Effect_Console from "../Effect.Console/index.js";
var main = function __do() {
    Effect_Console.log("Hello")();
    Effect_Console.log("Goodbye")();
    return Effect_Console.log("Done")();
};
export {
    main
};
