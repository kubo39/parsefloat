module parsefloat.slow;

import std.meta;
import std.range;
import std.traits;

import parsefloat.common;
import parsefloat.decimal;
import parsefloat.parse;

/// Parse the significant digits and biased, binary exponent of a float.
///
/// This is a fallback algorithm that uses a big-integer representation
/// of the float, and therefore is considerably slower than faster
/// approximations. However, it will always determine how to round
/// the significant digits to the nearest machine float, allowing
/// use to handle near half-way cases.
///
/// Near half-way cases are halfway between two consecutive machine floats.
/// For example, the float `16777217.0` has a bitwise representation of
/// `100000000000000000000000 1`. Rounding to a single-precision float,
/// the trailing `1` is truncated. Using round-nearest, tie-even, any
/// value above `16777217.0` must be rounded up to `16777218.0`, while
/// any value before or equal to `16777217.0` must be rounded down
/// to `16777216.0`. These near-halfway conversions therefore may require
/// a large number of digits to unambiguously determine how to round.
///
/// The algorithms described here are based on "Processing Long Numbers Quickly",
/// available here: <https://arxiv.org/pdf/2101.11408.pdf#section.11>.

private enum size_t MAX_SHIFT = 60;

///
private size_t getShift(size_t n)
{
    enum size_t NUM_POWERS = 19;
    const ubyte[19] POWERS =
        [0, 3, 6, 9, 13, 16, 19, 23, 26, 29, 33, 36, 39, 43, 46, 49, 53, 56, 59];
    return n < NUM_POWERS ? cast(size_t)POWERS[n] : MAX_SHIFT;
}

///
BiasedFp parseLongMantissa(T, Source)(ref Source source)
if (isInputRange!Source &&
    !is(Source == enum) &&
    (is(T == float) || is(T == double)))
{
    static if (is(T == double))
    {
        enum size_t MANTISSA_EXPLICIT_BITS = 52;
        enum int MIN_EXPONENT_ROUND_TO_EVEN = -4;
        enum int MAX_EXPONENT_ROUND_TO_EVEN = 23;
        enum int MINIMUM_EXPONENT = -1023;
        enum int INFINITE_POWER = 0x7FF;
        enum int SMALLEST_POWER_OF_TEN = -342;
        enum int LARGEST_POWER_OF_TEN = 308;
    }
    else static if (is(T == float))
    {
        enum size_t MANTISSA_EXPLICIT_BITS = 23;
        enum int MIN_EXPONENT_ROUND_TO_EVEN = -17;
        enum int MAX_EXPONENT_ROUND_TO_EVEN = 10;
        enum int MINIMUM_EXPONENT = -127;
        enum int INFINITE_POWER = 0xFF;
        enum int SMALLEST_POWER_OF_TEN = -65;
        enum int LARGEST_POWER_OF_TEN = 38;
    }

    const BiasedFp fpZero = { f: 0, e: 0 };
    const BiasedFp fpInf = { f: 0, e: INFINITE_POWER };

    auto d = parseDecimal(source);

    // Short-circuit if the value can only be a literal 0 or infinity.
    if (d.numDigits == 0 || d.decimalPoint < -324)
    {
        return fpZero;
    }
    else if (d.decimalPoint >= 310)
    {
        return fpInf;
    }
    int exp2 = 0;
    // Shift right toward (1/2 ... 1].
    while (d.decimalPoint > 0)
    {
        const size_t n = d.decimalPoint;
        const shift = getShift(n);
        d.rightShift(shift);
        if (d.decimalPoint < -DECIMAL_POINT_RANGE)
        {
            return fpZero;
        }
        exp2 += shift;
    }
    // Shift left toward (1/2 ... 1].
    while (d.decimalPoint <= 0)
    {
        size_t shift = void;
        if (d.decimalPoint == 0)
        {
            if (d.digits[0] >= 5)
            {
                shift = d.digits[0];
                break;
            }
            else if (d.digits[0] == 0 || d.digits[0] == 1)
                shift = 2;
            else
                shift = 1;
        }
        else
        {
            shift = getShift(-d.decimalPoint);
        }
        d.leftShift(shift);
        if (d.decimalPoint > DECIMAL_POINT_RANGE)
            return fpInf;
        exp2 -= cast(int) shift;
    }
    // We are now in the range [1/2 ... 1] but the binary format uses [1 ... 2].
    exp2--;
    while ((MINIMUM_EXPONENT + 1) > exp2)
    {
        size_t n = (MINIMUM_EXPONENT + 1) - exp2;
        if (n > MAX_SHIFT)
        {
            n = MAX_SHIFT;
        }
        d.rightShift(n);
        exp2 += cast(int) n;
    }
    if ((exp2 - MINIMUM_EXPONENT) >= INFINITE_POWER)
    {
        return fpInf;
    }
    // Shift the decimal to the hidden bit, and then round the value
    // to get the high mantissa+1 bits.
    d.leftShift(MANTISSA_EXPLICIT_BITS + 1);
    auto mantissa = d.round();
    if (mantissa >= (1UL << (MANTISSA_EXPLICIT_BITS + 1)))
    {
        // Rounding up overflowed to the carry bit, need to
        // shift back to the hidden bit.
        d.rightShift(1);
        exp2++;
        mantissa = d.round();
        if ((exp2 - MINIMUM_EXPONENT) >= INFINITE_POWER)
            return fpInf;
    }
    auto power2 = exp2 - MINIMUM_EXPONENT;
    if (mantissa < (1UL << MANTISSA_EXPLICIT_BITS))
        power2--;
    // Zero out all the bits above the explicit mantissa bits.
    mantissa &= (1UL << MANTISSA_EXPLICIT_BITS) - 1;
    return BiasedFp(mantissa, power2);
}
