import * as Effect_Console from "../Effect.Console/index.js";
import * as Safe_Coerce from "../Safe.Coerce/index.js";
var coerce = /* #__PURE__ */ Safe_Coerce.coerce();
var RoleNotReserved = /* #__PURE__ */ (function () {
    function RoleNotReserved(value0) {
        this.value0 = value0;
    };
    RoleNotReserved.create = function (value0) {
        return new RoleNotReserved(value0);
    };
    return RoleNotReserved;
})();
var RecursiveRepresentational = function (x) {
    return x;
};
var Rec5 = function (x) {
    return x;
};
var Rec4 = function (x) {
    return x;
};
var Rec3 = /* #__PURE__ */ (function () {
    function Rec3(value0) {
        this.value0 = value0;
    };
    Rec3.create = function (value0) {
        return new Rec3(value0);
    };
    return Rec3;
})();
var Rec2 = /* #__PURE__ */ (function () {
    function Rec2(value0) {
        this.value0 = value0;
    };
    Rec2.create = function (value0) {
        return new Rec2(value0);
    };
    return Rec2;
})();
var Rec1 = /* #__PURE__ */ (function () {
    function Rec1(value0) {
        this.value0 = value0;
    };
    Rec1.create = function (value0) {
        return new Rec1(value0);
    };
    return Rec1;
})();
var RankN4 = /* #__PURE__ */ (function () {
    function RankN4(value0) {
        this.value0 = value0;
    };
    RankN4.create = function (value0) {
        return new RankN4(value0);
    };
    return RankN4;
})();
var RankN3 = /* #__PURE__ */ (function () {
    function RankN3(value0) {
        this.value0 = value0;
    };
    RankN3.create = function (value0) {
        return new RankN3(value0);
    };
    return RankN3;
})();
var RankN2 = /* #__PURE__ */ (function () {
    function RankN2(value0) {
        this.value0 = value0;
    };
    RankN2.create = function (value0) {
        return new RankN2(value0);
    };
    return RankN2;
})();
var RankN1 = function (x) {
    return x;
};
var Phantom = /* #__PURE__ */ (function () {
    function Phantom() {

    };
    Phantom.value = new Phantom();
    return Phantom;
})();
var Phantom1 = function (x) {
    return x;
};
var Roles1 = function (x) {
    return x;
};
var NTString2 = function (x) {
    return x;
};
var NTString1 = function (x) {
    return x;
};
var NTInt1 = function (x) {
    return x;
};
var NTFn2 = function (x) {
    return x;
};
var NTFn1 = function (x) {
    return x;
};
var MyMap = /* #__PURE__ */ (function () {
    function MyMap(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    MyMap.create = function (value0) {
        return function (value1) {
            return new MyMap(value0, value1);
        };
    };
    return MyMap;
})();
var MutuallyRecursiveRepresentational1 = /* #__PURE__ */ (function () {
    function MutuallyRecursiveRepresentational1(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    MutuallyRecursiveRepresentational1.create = function (value0) {
        return function (value1) {
            return new MutuallyRecursiveRepresentational1(value0, value1);
        };
    };
    return MutuallyRecursiveRepresentational1;
})();
var MutuallyRecursiveRepresentational2 = /* #__PURE__ */ (function () {
    function MutuallyRecursiveRepresentational2(value0) {
        this.value0 = value0;
    };
    MutuallyRecursiveRepresentational2.create = function (value0) {
        return new MutuallyRecursiveRepresentational2(value0);
    };
    return MutuallyRecursiveRepresentational2;
})();
var MutuallyRecursivePhantom1 = /* #__PURE__ */ (function () {
    function MutuallyRecursivePhantom1(value0) {
        this.value0 = value0;
    };
    MutuallyRecursivePhantom1.create = function (value0) {
        return new MutuallyRecursivePhantom1(value0);
    };
    return MutuallyRecursivePhantom1;
})();
var MutuallyRecursivePhantom2 = /* #__PURE__ */ (function () {
    function MutuallyRecursivePhantom2(value0) {
        this.value0 = value0;
    };
    MutuallyRecursivePhantom2.create = function (value0) {
        return new MutuallyRecursivePhantom2(value0);
    };
    return MutuallyRecursivePhantom2;
})();
var Id2 = function (x) {
    return x;
};
var Id1 = function (x) {
    return x;
};
var D = /* #__PURE__ */ (function () {
    function D(value0) {
        this.value0 = value0;
    };
    D.create = function (value0) {
        return new D(value0);
    };
    return D;
})();
var NTD = function (x) {
    return x;
};
var Constrained2 = /* #__PURE__ */ (function () {
    function Constrained2(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Constrained2.create = function (value0) {
        return function (value1) {
            return new Constrained2(value0, value1);
        };
    };
    return Constrained2;
})();
var Constrained1 = /* #__PURE__ */ (function () {
    function Constrained1(value0) {
        this.value0 = value0;
    };
    Constrained1.create = function (value0) {
        return new Constrained1(value0);
    };
    return Constrained1;
})();
var Arr1 = /* #__PURE__ */ (function () {
    function Arr1(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Arr1.create = function (value0) {
        return function (value1) {
            return new Arr1(value0, value1);
        };
    };
    return Arr1;
})();
var ApPolykind = function (x) {
    return x;
};
var Ap = function (x) {
    return x;
};
var unwrapRec4 = coerce;
var underD = coerce;
var transSymm = function () {
    return function () {
        return function (v) {
            return coerce;
        };
    };
};
var trans$prime$prime = function () {
    return function () {
        return function () {
            return function (v) {
                return function (v1) {
                    return coerce;
                };
            };
        };
    };
};
var trans$prime = function () {
    return function () {
        return function (v) {
            return coerce;
        };
    };
};
var trans = function () {
    return function () {
        return function (v) {
            return coerce;
        };
    };
};
var toNT1Array = function () {
    return coerce;
};
var toNT1 = function () {
    return coerce;
};
var testRolesNotReserved = function (nominal) {
    return function (representational) {
        return function (phantom) {
            return "";
        };
    };
};
var testRoleNotReserved = function (role) {
    return role;
};
var symm = function () {
    return coerce;
};
var stringToNt1 = coerce;
var roles1ToSecond = coerce;
var refl = coerce;
var recursiveRepresentational = function () {
    return coerce;
};
var rec8ToRec8$prime = function () {
    return coerce;
};
var rec8ToRec8 = coerce;
var rec7ToRec7 = coerce;
var rec6ToRec6 = coerce;
var rec3ToRec3 = coerce;
var rec2ToRec2 = coerce;
var rec1ToRec1 = coerce;
var rankN4ToRankN4 = coerce;
var rankN3ToRankN3 = coerce;
var rankN2ToRankN2 = coerce;
var rankN1ToRankN1 = coerce;
var phantom1TypeToPhantom1Symbol = coerce;
var phantom1ToId12 = coerce;
var ntdToNTD = coerce;
var ntFn1ToNTFn2 = coerce;
var nt2ToNT1 = coerce;
var nt1ToString = coerce;
var nested = coerce;
var mutuallyRecursiveRepresentational = coerce;
var mutuallyRecursivePhantom = coerce;
var mapToMap = function () {
    return coerce;
};
var mapStringToMapString = /* #__PURE__ */ mapToMap();
var main = /* #__PURE__ */ Effect_Console.log(/* #__PURE__ */ coerce("Done"));
var libReExportedCtorToId2 = coerce;
var libHiddenCtorRepresentational = function () {
    return coerce;
};
var libExposedCtorToId2 = coerce;
var id2NTToId1Nt = coerce;
var id2NTToId1Int = coerce;
var id2IntToId1Int = coerce;
var id1ToId2 = coerce;
var id1IntToInt = coerce;
var id12ToId21 = coerce;
var givenCanonicalSameTyVarEq = function () {
    return function () {
        return function (v) {
            return coerce;
        };
    };
};
var givenCanonicalDiffTyVarEq2 = function () {
    return function () {
        return function (v) {
            return coerce;
        };
    };
};
var givenCanonicalDiffTyVarEq1 = function () {
    return function () {
        return coerce;
    };
};
var foreign2ToForeign2 = coerce;
var foreign1ToForeign1 = coerce;
var dToNTD = coerce;
var constrained1ToConstrained1 = coerce;
var arr1ToArr1Phantom = coerce;
var arr1ToArr1 = coerce;
var apRec4ToApRec5 = coerce;
var apPolykind = coerce;
var apId1ToApId2 = coerce;
var apId1ToApId1 = function () {
    return coerce;
};
export {
    refl,
    symm,
    trans,
    trans$prime,
    trans$prime$prime,
    transSymm,
    NTString1,
    nt1ToString,
    stringToNt1,
    toNT1,
    toNT1Array,
    NTString2,
    nt2ToNT1,
    Id1,
    Id2,
    id1ToId2,
    id12ToId21,
    Ap,
    apId1ToApId1,
    apId1ToApId2,
    ApPolykind,
    apPolykind,
    Phantom1,
    phantom1TypeToPhantom1Symbol,
    phantom1ToId12,
    nested,
    id1IntToInt,
    id2IntToId1Int,
    NTInt1,
    id2NTToId1Nt,
    id2NTToId1Int,
    NTFn1,
    NTFn2,
    ntFn1ToNTFn2,
    libExposedCtorToId2,
    libReExportedCtorToId2,
    libHiddenCtorRepresentational,
    Roles1,
    roles1ToSecond,
    D,
    underD,
    givenCanonicalSameTyVarEq,
    givenCanonicalDiffTyVarEq1,
    givenCanonicalDiffTyVarEq2,
    NTD,
    dToNTD,
    ntdToNTD,
    RankN1,
    rankN1ToRankN1,
    RankN2,
    rankN2ToRankN2,
    RankN3,
    rankN3ToRankN3,
    RankN4,
    rankN4ToRankN4,
    Phantom,
    Rec1,
    rec1ToRec1,
    Rec2,
    rec2ToRec2,
    Rec3,
    rec3ToRec3,
    Rec4,
    unwrapRec4,
    Rec5,
    apRec4ToApRec5,
    rec6ToRec6,
    rec7ToRec7,
    rec8ToRec8,
    rec8ToRec8$prime,
    Arr1,
    arr1ToArr1,
    arr1ToArr1Phantom,
    foreign1ToForeign1,
    foreign2ToForeign2,
    MyMap,
    mapToMap,
    mapStringToMapString,
    Constrained1,
    constrained1ToConstrained1,
    Constrained2,
    testRoleNotReserved,
    testRolesNotReserved,
    RoleNotReserved,
    RecursiveRepresentational,
    recursiveRepresentational,
    MutuallyRecursivePhantom1,
    MutuallyRecursivePhantom2,
    mutuallyRecursivePhantom,
    MutuallyRecursiveRepresentational1,
    MutuallyRecursiveRepresentational2,
    mutuallyRecursiveRepresentational,
    main
};
