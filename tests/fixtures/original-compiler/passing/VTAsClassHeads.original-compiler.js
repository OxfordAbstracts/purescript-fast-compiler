import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Array_NonEmpty from "../Data.Array.NonEmpty/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Traversable from "../Data.Traversable/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Console from "../Effect.Console/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showBoolean);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var intercalate = /* #__PURE__ */ Data_Array.intercalate(Data_Monoid.monoidString);
var B2 = /* #__PURE__ */ (function () {
    function B2() {

    };
    B2.value = new B2();
    return B2;
})();
var A2 = /* #__PURE__ */ (function () {
    function A2() {

    };
    A2.value = new A2();
    return A2;
})();
var superclassB2 = /* #__PURE__ */ (function () {
    return {
        superClassValue: B2.value
    };
})();
var superclassA2 = /* #__PURE__ */ (function () {
    return {
        superClassValue: A2.value
    };
})();
var singletonString = {
    singleton: "string"
};
var singletonInt = {
    singleton: "int"
};
var multiWithFDsStringInt = {
    multiWithFDs: 1
};
var multiWithFDsIntInt = {
    multiWithFDs: 0
};
var multiWithBidiFDsStringStr = {
    multiWithBidiFDs: 1
};
var multiWithBidiFDsIntInt = {
    multiWithBidiFDs: 0
};
var multiNoFDsStringInt = {
    multiNoFds: 1
};
var multiNoFDsIntInt = {
    multiNoFds: 0
};
var multiCoveringSetsIntIntSt = {
    noneOfSets: 2,
    partialOfABSet: function (a) {
        return {
            c: show(a),
            d: "2"
        };
    },
    partialOfFESet: function (f) {
        return {
            c: show1(f),
            d: "2"
        };
    }
};
var multiCoveringSetsBooleanB = {
    noneOfSets: 1,
    partialOfABSet: function (a) {
        return {
            c: (function () {
                if (a) {
                    return "101";
                };
                return "100";
            })(),
            d: "1"
        };
    },
    partialOfFESet: function (f) {
        return {
            c: show(f),
            d: "1"
        };
    }
};
var mainClassB2 = {
    mainClassInt: 3,
    Superclass0: function () {
        return superclassB2;
    }
};
var mainClassA2 = {
    mainClassInt: 0,
    Superclass0: function () {
        return superclassA2;
    }
};
var eqB2 = {
    eq: function (x) {
        return function (y) {
            return true;
        };
    }
};
var eqA2 = {
    eq: function (x) {
        return function (y) {
            return true;
        };
    }
};
var conflictingIdentSynonymSt = {
    conflictingIdentSynonym: function (v) {
        return 1;
    }
};
var conflictingIdentSynonymIn = {
    conflictingIdentSynonym: function (v) {
        return 2;
    }
};
var conflictingIdentString = {
    conflictingIdent: function (v) {
        return 1;
    }
};
var conflictingIdentInt = {
    conflictingIdent: function (v) {
        return 2;
    }
};
var superClassValue = function (dict) {
    return dict.superClassValue;
};
var singleton = function (dict) {
    return dict.singleton;
};
var singletonWorks = /* #__PURE__ */ (function () {
    var right = singleton(singletonString);
    var left = singleton(singletonInt);
    return pure((function () {
        var $70 = left !== right;
        if ($70) {
            return Data_Maybe.Nothing.value;
        };
        return new Data_Maybe.Just("Singleton failed");
    })());
})();
var partialOfFESet = function (dict) {
    return dict.partialOfFESet;
};
var partialOfABSet = function (dict) {
    return dict.partialOfABSet;
};
var noneOfSets = function (dict) {
    return dict.noneOfSets;
};
var multiWithFDs = function (dict) {
    return dict.multiWithFDs;
};
var multiWithFdsWorks = /* #__PURE__ */ pure(/* #__PURE__ */ (function () {
    var $75 = multiWithFDs(multiWithFDsIntInt) !== multiWithFDs(multiWithFDsStringInt);
    if ($75) {
        return Data_Maybe.Nothing.value;
    };
    return new Data_Maybe.Just("MultiWithFds failed");
})());
var multiWithBidiFDs = function (dict) {
    return dict.multiWithBidiFDs;
};
var multiWithBidiFDsLeftWorks = /* #__PURE__ */ pure(/* #__PURE__ */ (function () {
    var $77 = multiWithBidiFDs(multiWithBidiFDsIntInt) !== multiWithBidiFDs(multiWithBidiFDsStringStr);
    if ($77) {
        return Data_Maybe.Nothing.value;
    };
    return new Data_Maybe.Just("MultiWithFds failed");
})());
var multiWithBidiFDsRightWorks = /* #__PURE__ */ (function () {
    var right = multiWithBidiFDs(multiWithBidiFDsStringStr);
    var left = multiWithBidiFDs(multiWithBidiFDsIntInt);
    return pure((function () {
        var $78 = left !== right;
        if ($78) {
            return Data_Maybe.Nothing.value;
        };
        return new Data_Maybe.Just("MultiWithFds failed");
    })());
})();
var multiNoFds = function (dict) {
    return dict.multiNoFds;
};
var multiNoFdsWorks = /* #__PURE__ */ (function () {
    var right = multiNoFds(multiNoFDsStringInt);
    var left = multiNoFds(multiNoFDsIntInt);
    return pure((function () {
        var $80 = left !== right;
        if ($80) {
            return Data_Maybe.Nothing.value;
        };
        return new Data_Maybe.Just("MultiNoFDs failed");
    })());
})();
var multiCoveringSetsWorks = /* #__PURE__ */ (function () {
    var test2c = show1(false) === (partialOfFESet(multiCoveringSetsIntIntSt)(false)).c;
    var test2b = show(20) === (partialOfABSet(multiCoveringSetsIntIntSt)(20)).c;
    var test2a = 2 === noneOfSets(multiCoveringSetsIntIntSt);
    var test1c = show(3) === (partialOfFESet(multiCoveringSetsBooleanB)(3)).c;
    var test1b = "101" === (partialOfABSet(multiCoveringSetsBooleanB)(true)).c;
    var test1a = 1 === noneOfSets(multiCoveringSetsBooleanB);
    var passes = test1a && (test1b && (test1c && (test2a && (test2b && test2c))));
    return pure((function () {
        if (passes) {
            return Data_Maybe.Nothing.value;
        };
        return new Data_Maybe.Just("MultiCoveringSets failed");
    })());
})();
var mainClassInt = function (dict) {
    return dict.mainClassInt;
};
var mainClassWorks = /* #__PURE__ */ (function () {
    var test2 = Data_Eq.eq(eqA2)(A2.value)(superClassValue(superclassA2));
    var test1 = 0 === mainClassInt(mainClassA2);
    return pure((function () {
        var $83 = test1 && test2;
        if ($83) {
            return Data_Maybe.Nothing.value;
        };
        return new Data_Maybe.Just("MainClass failed");
    })());
})();
var conflictingIdentSynonym = function (dict) {
    return dict.conflictingIdentSynonym;
};
var conflictingIdentSynonymWorks = /* #__PURE__ */ pure(/* #__PURE__ */ (function () {
    var $85 = 1 === conflictingIdentSynonym(conflictingIdentSynonymSt)(4);
    if ($85) {
        return Data_Maybe.Nothing.value;
    };
    return new Data_Maybe.Just("ConflictingIdentSynonym failed");
})());
var conflictingIdent = function (dict) {
    return dict.conflictingIdent;
};
var conflictingIdentWorks = /* #__PURE__ */ pure(/* #__PURE__ */ (function () {
    var $87 = 1 === conflictingIdent(conflictingIdentString)(4);
    if ($87) {
        return Data_Maybe.Nothing.value;
    };
    return new Data_Maybe.Just("ConflictingIdent failed");
})());
var main = function __do() {
    var arr$prime = Data_Traversable.sequence(Data_Traversable.traversableArray)(Effect.applicativeEffect)([ singletonWorks, conflictingIdentWorks, conflictingIdentSynonymWorks, multiNoFdsWorks, multiWithFdsWorks, multiWithBidiFDsLeftWorks, multiWithBidiFDsRightWorks, mainClassWorks ])();
    var v = Data_Array_NonEmpty.fromArray(Data_Array.catMaybes(arr$prime));
    if (v instanceof Data_Maybe.Just) {
        return Effect_Console.log("Errors..." + intercalate("\x0a")(Data_Array_NonEmpty.toArray(v.value0)))();
    };
    if (v instanceof Data_Maybe.Nothing) {
        return Effect_Console.log("Done")();
    };
    throw new Error("Failed pattern match at Main (line 192, column 3 - line 196, column 17): " + [ v.constructor.name ]);
};
export {
    conflictingIdent,
    conflictingIdentSynonym,
    mainClassInt,
    multiNoFds,
    multiWithBidiFDs,
    multiWithFDs,
    noneOfSets,
    partialOfABSet,
    partialOfFESet,
    singleton,
    superClassValue,
    singletonWorks,
    conflictingIdentWorks,
    conflictingIdentSynonymWorks,
    multiNoFdsWorks,
    multiWithFdsWorks,
    multiWithBidiFDsLeftWorks,
    multiWithBidiFDsRightWorks,
    A2,
    B2,
    mainClassWorks,
    multiCoveringSetsWorks,
    main,
    singletonInt,
    singletonString,
    conflictingIdentString,
    conflictingIdentInt,
    conflictingIdentSynonymSt,
    conflictingIdentSynonymIn,
    multiNoFDsIntInt,
    multiNoFDsStringInt,
    multiWithFDsIntInt,
    multiWithFDsStringInt,
    multiWithBidiFDsIntInt,
    multiWithBidiFDsStringStr,
    eqA2,
    superclassA2,
    mainClassA2,
    eqB2,
    superclassB2,
    mainClassB2,
    multiCoveringSetsBooleanB,
    multiCoveringSetsIntIntSt
};
