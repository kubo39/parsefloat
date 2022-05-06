module parsefloat.number;

struct Number
{
    long exponent;
    ulong mantissa;
    bool manyDigits;
    size_t count;
}

package:

/// Detect if the float can be accurately reconstructed from native floats.
bool isFastPath(Target)(Number number)
if (is(Target == float) || is(Target == double))
{
    static if (is(Target == float))
    {
        long MIN_EXPONENT_FAST_PATH = -10; // assuming FLT_EVAL_METHOD = 0
        long MAX_EXPONENT_DISGUISED_FAST_PATH;
        size_t MANTISSA_EXPLICIT_BITS = 23;
    }
    else static if (is(Target == double))
    {
        long MIN_EXPONENT_FAST_PATH = -22; // assuming FLT_EVAL_METHOD = 0
        long MAX_EXPONENT_DISGUISED_FAST_PATH = 37;
        size_t MANTISSA_EXPLICIT_BITS = 52;
    }
    ulong MAX_MANTISSA_FAST_PATH = 2UL << MANTISSA_EXPLICIT_BITS;
    return MIN_EXPONENT_FAST_PATH <= number.exponent
        && number.exponent <= MAX_EXPONENT_DISGUISED_FAST_PATH
        && number.mantissa <= MAX_MANTISSA_FAST_PATH
        && !number.manyDigits;
}


immutable ulong[16] INT_POW10 = [
    1,
    10,
    100,
    1000,
    10000,
    100000,
    1000000,
    10000000,
    100000000,
    1000000000,
    10000000000,
    100000000000,
    1000000000000,
    10000000000000,
    100000000000000,
    1000000000000000
];

T pow10FastPath(T)(size_t exp) if (is(T == float))
{
    static float[16] TABLE =
        [1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7,
         1e8, 1e9, 1e10, 0.0, 0.0, 0.0, 0.0, 0.0];
    return TABLE[exp & 15];
}

T pow10FastPath(T)(size_t exp) if (is(T == double))
{
    static double[32] TABLE = [
        1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7,
        1e8, 1e9, 1e10, 1e11, 1e12, 1e13, 1e14, 1e15,
        1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22, 0.0,
        0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
    return TABLE[exp & 31];
}

/// The fast path algorithm using machine-sized integers and floats.
///
/// This is extracted into a separate function so that it can be attempted before constructing
/// a Decimal. This only works if both the mantissa and the exponent
/// can be exactly represented as a machine float, since IEE-754 guarantees
/// no rounding will occur.
///
/// There is an exception: disguised fast-path cases, where we can shift
/// powers-of-10 from the exponent to the significant digits.
bool tryFastPath(Target)(Number number, ref Target value)
if (is(Target == float) || is(Target == double))
{
    static if (is(Target == float))
    {
        enum size_t MANTISSA_EXPLICIT_BITS = 23;
        enum long MAX_EXPONENT_FAST_PATH = 10;
        enum ulong MAX_MANTISSA_FAST_PATH = 2UL << MANTISSA_EXPLICIT_BITS;
    }
    else static if (is(Target == double))
    {
        enum size_t MANTISSA_EXPLICIT_BITS = 52;
        enum long MAX_EXPONENT_FAST_PATH = 22;
        enum ulong MAX_MANTISSA_FAST_PATH = 2UL << MANTISSA_EXPLICIT_BITS;
    }

    // TODO: x86 (no SSE/SSE2) requires x87 FPU to be setup correctly with fldcw

    if (!isFastPath!(Target)(number))
        return false;

    if (number.exponent <= MAX_EXPONENT_FAST_PATH)
    {
        // normal fast path
        assert(number.mantissa <= MAX_MANTISSA_FAST_PATH);
        value = cast(Target) number.mantissa;
        if (number.exponent < 0)
            value = value / pow10FastPath!Target(-number.exponent);
        else
            value = value * pow10FastPath!Target(number.exponent);
    }
    else
    {
        // disguised fast path
        const shift = number.exponent - MAX_EXPONENT_FAST_PATH;
        const mantissa = number.mantissa * INT_POW10[shift];
        if (mantissa > MAX_MANTISSA_FAST_PATH)
            return false;
        value = cast(Target) mantissa * pow10FastPath!Target(MAX_EXPONENT_FAST_PATH);
    }
    return true;
}

