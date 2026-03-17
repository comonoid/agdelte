// Contains *most* of the primitives required by the JavaScript backend.
// (Some, e.g., those using Agda types like Maybe, are defined in their
// respective builtin modules.)
//
// Primitives prefixed by 'u' are uncurried variants, which are sometimes
// emitted by the JavaScript backend. Whenever possible, the curried primitives
// should be implemented in terms of the uncurried ones.
//
// Primitives prefixed by '_' are internal variants, usually for those primitives
// which return Agda types like Maybe. These are never emitted by the compiler,
// but can be used internally to define other prefixes.

// Integers

// primIntegerFromString : String -> Int
exports.primIntegerFromString = BigInt;

// primShowInteger : Int -> String
exports.primShowInteger = x => x.toString();

// uprimIntegerPlus : (Int, Int) -> Int
exports.uprimIntegerPlus = (x, y) => x + y;

// uprimIntegerMinus : (Int, Int) -> Int
exports.uprimIntegerMinus = (x, y) => x - y;

// uprimIntegerMultiply : (Int, Int) -> Int
exports.uprimIntegerMultiply = (x, y) => x * y;

// uprimIntegerRem : (Int, Int) -> Int
exports.uprimIntegerRem = (x, y) => x % y;

// uprimIntegerQuot : (Int, Int) -> Int
exports.uprimIntegerQuot = (x, y) => x / y;

// uprimIntegerEqual : (Int, Int) -> Bool
exports.uprimIntegerEqual = (x, y) => x === y;

// uprimIntegerGreaterOrEqualThan : (Int, Int) -> Bool
exports.uprimIntegerGreaterOrEqualThan = (x, y) => x >= y;

// uprimIntegerLessThan : (Int, Int) -> Bool
exports.uprimIntegerLessThan = (x, y) => x < y;

// Words
const WORD64_MAX_VALUE = 18446744073709551616n;

// primWord64ToNat : Word64 -> Nat
exports.primWord64ToNat = x => x;

// primWord64FromNat : Nat -> Word64
exports.primWord64FromNat = x => x % WORD64_MAX_VALUE;

// uprimWord64Plus : (Word64, Word64) -> Word64
exports.uprimWord64Plus = (x, y) => (x + y) % WORD64_MAX_VALUE;

// uprimWord64Minus : (Word64, Word64) -> Word64
exports.uprimWord64Minus = (x, y) => (x + WORD64_MAX_VALUE - y) % WORD64_MAX_VALUE;

// uprimWord64Multiply : (Word64, Word64) -> Word64
exports.uprimWord64Multiply = (x, y) => (x * y) % WORD64_MAX_VALUE;

// Natural numbers

// primNatMinus : Nat -> Nat -> Nat
exports.primNatMinus = x => y => {
  const z = x - y;
  return z < 0n ? 0n : z;
};

// Floating-point numbers
var _primFloatGreatestCommonFactor = function(x, y) {
    var z;
    x = Math.abs(x);
    y = Math.abs(y);
    while (y) {
        z = x % y;
        x = y;
        y = z;
    }
    return x;
};
exports._primFloatRound = function(x) {
    if (exports.primFloatIsNaN(x) || exports.primFloatIsInfinite(x)) {
        return null;
    }
    else {
        return BigInt(Math.round(x));
    }
};
exports._primFloatFloor = function(x) {
    if (exports.primFloatIsNaN(x) || exports.primFloatIsInfinite(x)) {
        return null;
    }
    else {
        return BigInt(Math.floor(x));
    }
};
exports._primFloatCeiling = function(x) {
    if (exports.primFloatIsNaN(x) || exports.primFloatIsInfinite(x)) {
        return null;
    }
    else {
        return BigInt(Math.ceil(x));
    }
};
exports._primFloatToRatio = function(x) {
    if (exports.primFloatIsNaN(x)) {
        return {numerator: BigInt(0), denominator: BigInt(0)};
    }
    else if (x < 0.0 && exports.primFloatIsInfinite(x)) {
        return {numerator: BigInt(-1), denominator: BigInt(0)};
    }
    else if (x > 0.0 && exports.primFloatIsInfinite(x)) {
        return {numerator: BigInt(1), denominator: BigInt(0)};
    }
    else if (exports.primFloatIsNegativeZero(x)) {
        return {numerator: BigInt(0), denominator: BigInt(1)};
    }
    else if (x == 0.0) {
        return {numerator: BigInt(0), denominator: BigInt(1)};
    }
    else {
        // Exact decomposition: x = mantissa * 2^exponent (from _primFloatDecode)
        var decoded = exports._primFloatDecode(x);
        if (decoded === null) return {numerator: BigInt(0), denominator: BigInt(0)};
        var m = decoded.mantissa;   // BigInt
        var e = decoded.exponent;   // BigInt
        if (e >= 0n) {
            return {numerator: m * (2n ** e), denominator: 1n};
        } else {
            return {numerator: m, denominator: 2n ** (-e)};
        }
    }
};
exports._primFloatDecode = function(x) {
    if (exports.primFloatIsNaN(x)) {
        return null;
    }
    else if (x < 0.0 && exports.primFloatIsInfinite(x)) {
        return null;
    }
    else if (x > 0.0 && exports.primFloatIsInfinite(x)) {
        return null;
    }
    else if (x === 0) {
        return {mantissa: 0n, exponent: 0n};
    }
    else {
        var mantissa = x, exponent = 0;
        while (!Number.isInteger(mantissa)) {
            mantissa *= 2.0;
            exponent -= 1;
        };
        while (mantissa % 2.0 === 0) {
            mantissa /= 2.0;
            exponent += 1;
        }
        return {mantissa: BigInt(mantissa), exponent: BigInt(exponent)};
    }
};
exports.uprimFloatEquality = function(x, y) {
    return x === y;
};
exports.primFloatEquality = function(x) {
    return function(y) {
        return exports.uprimFloatEquality(x, y);
    };
};
exports.primFloatInequality = function(x) {
    return function(y) {
        return x <= y;
    };
};
exports.primFloatLess = function(x) {
    return function(y) {
        return x < y;
    };
};
exports.primFloatIsInfinite = function(x) {
    return !Number.isNaN(x) && !Number.isFinite(x);
};
exports.primFloatIsNaN = function(x) {
    return Number.isNaN(x);
};
exports.primFloatIsNegativeZero = function(x) {
    return Object.is(x,-0.0);
};
exports.primFloatIsSafeInteger = function(x) {
    return Number.isSafeInteger(x);
};


exports.primFloatToWord64 = function(x) {
    if (exports.primFloatIsNaN(x)) {
        return null;
    }
    // Use DataView to reinterpret float64 bits as uint64 (castDoubleToWord64).
    // This handles all cases correctly: ±Inf, ±0, normals, subnormals.
    var buf = new ArrayBuffer(8);
    var view = new DataView(buf);
    view.setFloat64(0, x);
    var hi = BigInt(view.getUint32(0));
    var lo = BigInt(view.getUint32(4));
    return (hi << 32n) | lo;
};

// primNatToFloat : Nat -> Float
exports.primNatToFloat = Number;

// primIntToFloat : Int -> Float
exports.primIntToFloat = Number;

// primRatioToFloat : Int -> Int -> Float
exports.primRatioToFloat = x => y => Number(x) / Number(y);

// uprimFloatEncode : (Int, Int) -> Maybe Float
exports.uprimFloatEncode = (x, y) => {
  const mantissa = Number(x);
  const exponent = Number(y);

  if (Number.isSafeInteger(mantissa) && -1024 <= exponent && exponent <= 1024) {
    return mantissa * (2 ** exponent);
  }

  else {
    return null;
  }
};

exports.primShowFloat = function(x) {
    // See Issue #2192.
    if (Number.isInteger(x)) {
        if (exports.primFloatIsNegativeZero(x)) {
            return ("-0.0");
        } else {
            return (x.toString() + ".0");
        }
    } else {
        return x.toString();
    }
};
exports.primFloatPlus = function(x) {
    return function(y) {
        return x + y;
    };
};
exports.primFloatMinus = function(x) {
    return function(y) {
        return x - y;
    };
};
exports.primFloatTimes = function(x) {
    return function(y) {
        return x * y;
    };
};
exports.primFloatNegate = function(x) {
    return -x;
};
exports.primFloatDiv = function(x) {
  return function(y) {
    return x / y;
  };
};
exports.primFloatPow = function(x) {
    return function(y) {
        return x ** y;
    };
};
exports.primFloatSqrt = function(x) {
    return Math.sqrt(x);
};
exports.primFloatExp = function(x) {
    return Math.exp(x);
};
exports.primFloatLog = function(x) {
    return Math.log(x);
};
exports.primFloatSin = function(x) {
    return Math.sin(x);
};
exports.primFloatCos = function(x) {
    return Math.cos(x);
};
exports.primFloatTan = function(x) {
    return Math.tan(x);
};
exports.primFloatASin = function(x) {
    return Math.asin(x);
};
exports.primFloatACos = function(x) {
    return Math.acos(x);
};
exports.primFloatATan = function(x) {
    return Math.atan(x);
};
exports.primFloatATan2 = function(x) {
    return function(y){
        return Math.atan2(x, y);
    };
};
exports.primFloatSinh = function(x) {
    return Math.sinh(x);
};
exports.primFloatCosh = function(x) {
    return Math.cosh(x);
};
exports.primFloatTanh = function(x) {
    return Math.tanh(x);
};
exports.primFloatASinh = function(x) {
    return Math.asinh(x);
};
exports.primFloatACosh = function(x) {
    return Math.acosh(x);
};
exports.primFloatATanh = function(x) {
    return Math.atanh(x);
};

// Cubical primitives.
exports.primIMin = x => y => x && y;
exports.primIMax = x => y => x || y;
exports.primINeg = x => !x;
exports.primPartial = _ => _ => x => x;
exports.primPartialP = _ => _ => x => x;
exports.primPOr = _ => i => _ => _ => x => y => i ? x : y;
exports.primComp = _ => _ => _ => _ => x => x;
exports.primTransp = _ => _ => _ => x => x;
exports.primHComp = _ => _ => _ => _ => x => x;
exports.primSubOut = _ => _ => _ => _ => x => x;
exports.prim_glueU = _ => _ => _ => _ => _ => x => x;
exports.prim_unglueU = _ => _ => _ => _ => x => x;
exports.primFaceForall = f => f(true) == true && f(false) == false;

// Other stuff

// primSeq : (X, Y) -> Y
exports.primSeq = (x, y) => y;

// uprimQNameEquality : (Name, Name) -> Bool
exports.uprimQNameEquality = (x, y) => x['id'] === y['id'] && x['moduleId'] === y['moduleId'];

// primQNameEquality : Name -> Name -> Bool
exports.primQNameEquality = x => y => exports.uprimQNameEquality(x, y);

// primQNameLess : Name -> Name -> Bool
exports.primQNameLess = x => y => x['id'] === y['id'] ? x['moduleId'] < y['moduleId'] : x['id'] < y['id'];

// primShowQName : Name -> String
exports.primShowQName = x => x['name'];

// primQNameFixity : Name -> Fixity
exports.primQNameFixity = x => x['fixity'];

// Meta

// primShowMeta : Meta -> String
//   Should be kept in sync with version in `primitiveFunctions` in
//   Agda.TypeChecking.Primitive
exports.primShowMeta = x => "_" + x['id'] + "@" + x['module'];

// primMetaToNat : Meta -> Nat
//   Should be kept in sync with `metaToNat` in Agda.TypeChecking.Primitive
exports.primMetaToNat = x => BigInt(x['module']) * 18446744073709551616n + BigInt(x['id']);

// primMetaEquality : Meta -> Meta -> Bool
exports.primMetaEquality = x => y => x['id'] === y['id'] && x['module'] === y['module'];

// primMetaLess : Meta -> Meta -> Bool
exports.primMetaLess = x => y => x['id'] === y['id'] ? x['module'] < y['module'] : x['id'] < y['id'];
