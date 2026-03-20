import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var point = {
    x: 1.0,
    y: 0.0
};
var getX = function (v) {
    return v.x;
};
var main = function __do() {
    Effect_Console.logShow(Data_Show.showNumber)(getX(point))();
    Effect_Console.log((function (v) {
        return v[" 123 string Prop Name "];
    })({
        " 123 string Prop Name ": "OK"
    }))();
    Effect_Console.log((function (v) {
        return v.y;
    })((function (v) {
        return v.x;
    })({
        x: {
            y: "Nested"
        }
    })))();
    return Effect_Console.log((function (v) {
        return v.value;
    })({
        value: "Done"
    }))();
};
export {
    getX,
    point,
    main
};
