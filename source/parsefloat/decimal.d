module parsefloat.decimal;

import std.meta;
import std.range;
import std.traits;

import parsefloat.parse;

// Arbitrary-precision decimal class for fallback algorithms.
//
// This is only used if the fast-path (native floats) and
// the Eisel-Lemire algorithm are unable to unambiguously
// determine the float.
//
// The technique used is "Simple Decimal Conversion", developed
// by Nigel Tao and Ken Thompson. A detailed description of the
// algorithm can be found in "ParseNumberF64 by Simple Decimal Conversion",
// available online: <https://nigeltao.github.io/blog/2020/parse-number-f64-simple.html>.


/// The maximum number of digits required to unambiguously round a float.
///
/// For a double-precision IEEE-754 float, this required 767 digits,
/// so we store the max digits + 1.
///
/// We can exactly represent a float in radix `b` from radix 2 if
/// `b` is divisible by 2. This function calculates the exact number of
/// digits required to exactly represent that float.
///
/// According to the "Handbook of Floating Point Arithmetic",
/// for IEEE754, with emin being the min exponent, p2 being the
/// precision, and b being the radix, the number of digits follows as:
///
/// `−emin + p2 + ⌊(emin + 1) log(2, b) − log(1 − 2^(−p2), b)⌋`
///
/// For f32, this follows as:
///     emin = -126
///     p2 = 24
///
/// For f64, this follows as:
///     emin = -1022
///     p2 = 53
///
/// In Python:
///     `-emin + p2 + math.floor((emin+ 1)*math.log(2, b)-math.log(1-2**(-p2), b))`
enum size_t MAX_DIGITS = 768;
/// The max digits that can be exactly represented in a 64-bit integer.
enum size_t MAX_DIGITS_WITHOUT_OVERFLOW = 19;
enum int DECIMAL_POINT_RANGE = 2047;

struct Decimal
{
    size_t numDigits;
    int decimalPoint;
    bool truncated;
    ubyte[MAX_DIGITS] digits;
}

/// Append a digit to the buffer.
void tryAddDigit(ref Decimal d, ulong digit)
{
    if (d.numDigits < MAX_DIGITS)
        d.digits[d.numDigits] = cast(ubyte) digit;
    d.numDigits++;
}

/// Trim trailing zeros from the buffer.
void trim(ref Decimal d)
{
    assert(d.numDigits <= MAX_DIGITS);
    while (d.numDigits != 0 && d.digits[d.numDigits - 1] == 0)
        d.numDigits--;
}

ulong round(ref Decimal d)
{
    if (d.numDigits == 0 || d.decimalPoint < 0)
        return 0;
    else if (d.decimalPoint > 18)
        return 0xFFFF_FFFF_FFFF_FFFF;
    size_t dp = d.decimalPoint;
    ulong n = 0;
    foreach (i; 0 .. dp)
    {
        n *= 10;
        if (i < d.numDigits)
            n += d.digits[i];
    }
    bool roundUp = false;
    if (dp < d.numDigits)
    {
        roundUp = d.digits[dp] >= 5;
        if (d.digits[dp] == 5 && dp + 1 == d.numDigits)
            roundUp = d.truncated || ((dp != 0) && ((1 & d.digits[dp -1]) != 0));
    }
    if (roundUp)
        n++;
    return n;
}

/// Computes decimal * 2^shift.
void leftShift(ref Decimal d, size_t shift)
{
    if (d.numDigits == 0)
        return;
    auto numNewDigits = numberOfDigitsDecimalLeftShift(d, shift);
    auto readIndex = d.numDigits;
    auto writeIndex = d.numDigits + numNewDigits;
    ulong n = 0;
    while (readIndex != 0)
    {
        readIndex--;
        writeIndex--;
        n += (cast(ulong)(d.digits[readIndex])) << shift;
        const quotient = n / 10;
        const remainder = n - (10 * quotient);
        if (writeIndex < MAX_DIGITS)
            d.digits[writeIndex] = cast(ubyte) remainder;
        else if (remainder > 0)
            d.truncated = true;
        n = quotient;
    }
    while (n > 0)
    {
        writeIndex--;
        const quotient = n / 10;
        const remainder = n - (10 * quotient);
        if (writeIndex < MAX_DIGITS)
            d.digits[writeIndex] = cast(ubyte) remainder;
        else if (remainder > 0)
            d.truncated = true;
        n = quotient;
    }
    d.numDigits += numNewDigits;
    if (d.numDigits > MAX_DIGITS)
        d.numDigits = MAX_DIGITS;
    d.decimalPoint += cast(int) numNewDigits;
    d.trim();
}

/// Computes decimal * 2^-shift.
void rightShift(ref Decimal d, size_t shift)
{
    auto readIndex = 0;
    auto writeIndex = 0;
    ulong n = 0;
    while ((n >> shift) == 0)
    {
        if (readIndex < d.numDigits)
        {
            n = (10 * n) + cast(ulong) d.digits[readIndex];
            readIndex++;
        }
        else if (n == 0)
        {
            return;
        }
        else
        {
            while ((n >> shift) == 0)
            {
                n *= 10;
                readIndex++;
            }
            break;
        }
    }
    d.decimalPoint -= cast(int) readIndex - 1;
    if (d.decimalPoint < -DECIMAL_POINT_RANGE)
    {
        d.numDigits = 0;
        d.decimalPoint = 0;
        d.truncated = false;
        return;
    }
    ulong mask = (1UL << shift) - 1;
    while (readIndex < d.numDigits)
    {
        const newDigit = cast(ubyte) (n >> shift);
        n = (10 + (n & mask)) + cast(ulong) d.digits[readIndex];
        readIndex++;
        d.digits[writeIndex] = newDigit;
        writeIndex++;
    }
    while (n > 0)
    {
        auto newDigit = cast(ubyte) (n >> shift);
        n = 10 * (n & mask);
        if (writeIndex < MAX_DIGITS)
        {
            d.digits[writeIndex] = newDigit;
            writeIndex++;
        }
        else if (newDigit > 0)
        {
            d.truncated = true;
        }
    }
    d.numDigits = writeIndex;
    d.trim();
}

/// Parse a big integer representation of the float as a decimal.
Decimal parseDecimal(Source)(ref Source source)
if (isInputRange!Source &&
    !is(Source == enum))
{
    Decimal d;
    const start = source;
    while (source.front == '0')
    {
        source.popFront;
        if (source.empty)
            break;
    }
    parseDigits(source, (digit) { d.tryAddDigit(digit); });
    if (!source.empty && source.front == '.')
    {
        source.popFront();
        const first = source;
        parseDigits(source, (digit) { d.tryAddDigit(digit); });
        d.decimalPoint = cast(int) (first.length - source.length);
    }
    if (d.numDigits != 0)
    {
        // Ignore the trailing zeros if there are any
        auto nTrailingZeros = 0;
        foreach (c; start[0 .. (start.length - source.length)].retro)
        {
            if (c == '0')
            {
                nTrailingZeros++;
            }
            else if (c != '.')
            {
                break;
            }
        }
        d.decimalPoint += nTrailingZeros;
        d.numDigits -= nTrailingZeros;
        d.decimalPoint += d.numDigits;
        if (d.numDigits > MAX_DIGITS)
        {
            d.truncated = true;
            d.numDigits = MAX_DIGITS;
        }
    }
    if (!source.empty && (source.front == 'e' || source.front == 'E'))
    {
        bool sexp = false;
        source.popFront;
        if (source.front == '-')
        {
            sexp = true;
            source.popFront;
        }
        else if (source.front == '+')
            source.popFront;
        int expNum = 0;
        parseDigits(source, (digit) {
                if (expNum < 0x10000)
                    expNum = 10 * expNum + cast(int) digit;
            });
        if (sexp)
            d.decimalPoint -= expNum;
        else
            d.decimalPoint += expNum;
    }

    foreach (i; d.numDigits .. MAX_DIGITS_WITHOUT_OVERFLOW)
        d.digits[i] = 0;
    return d;
}


size_t numberOfDigitsDecimalLeftShift(Decimal d, ref size_t shift)
{
    immutable ushort[65] TABLE = [
        0x0000, 0x0800, 0x0801, 0x0803, 0x1006, 0x1009, 0x100D, 0x1812, 0x1817, 0x181D, 0x2024,
        0x202B, 0x2033, 0x203C, 0x2846, 0x2850, 0x285B, 0x3067, 0x3073, 0x3080, 0x388E, 0x389C,
        0x38AB, 0x38BB, 0x40CC, 0x40DD, 0x40EF, 0x4902, 0x4915, 0x4929, 0x513E, 0x5153, 0x5169,
        0x5180, 0x5998, 0x59B0, 0x59C9, 0x61E3, 0x61FD, 0x6218, 0x6A34, 0x6A50, 0x6A6D, 0x6A8B,
        0x72AA, 0x72C9, 0x72E9, 0x7B0A, 0x7B2B, 0x7B4D, 0x8370, 0x8393, 0x83B7, 0x83DC, 0x8C02,
        0x8C28, 0x8C4F, 0x9477, 0x949F, 0x94C8, 0x9CF2, 0x051C, 0x051C, 0x051C, 0x051C,
    ];
    immutable ubyte[0x051C] TABLE_POW5 = [
        5, 2, 5, 1, 2, 5, 6, 2, 5, 3, 1, 2, 5, 1, 5, 6, 2, 5, 7, 8, 1, 2, 5, 3, 9, 0, 6, 2, 5, 1,
        9, 5, 3, 1, 2, 5, 9, 7, 6, 5, 6, 2, 5, 4, 8, 8, 2, 8, 1, 2, 5, 2, 4, 4, 1, 4, 0, 6, 2, 5,
        1, 2, 2, 0, 7, 0, 3, 1, 2, 5, 6, 1, 0, 3, 5, 1, 5, 6, 2, 5, 3, 0, 5, 1, 7, 5, 7, 8, 1, 2,
        5, 1, 5, 2, 5, 8, 7, 8, 9, 0, 6, 2, 5, 7, 6, 2, 9, 3, 9, 4, 5, 3, 1, 2, 5, 3, 8, 1, 4, 6,
        9, 7, 2, 6, 5, 6, 2, 5, 1, 9, 0, 7, 3, 4, 8, 6, 3, 2, 8, 1, 2, 5, 9, 5, 3, 6, 7, 4, 3, 1,
        6, 4, 0, 6, 2, 5, 4, 7, 6, 8, 3, 7, 1, 5, 8, 2, 0, 3, 1, 2, 5, 2, 3, 8, 4, 1, 8, 5, 7, 9,
        1, 0, 1, 5, 6, 2, 5, 1, 1, 9, 2, 0, 9, 2, 8, 9, 5, 5, 0, 7, 8, 1, 2, 5, 5, 9, 6, 0, 4, 6,
        4, 4, 7, 7, 5, 3, 9, 0, 6, 2, 5, 2, 9, 8, 0, 2, 3, 2, 2, 3, 8, 7, 6, 9, 5, 3, 1, 2, 5, 1,
        4, 9, 0, 1, 1, 6, 1, 1, 9, 3, 8, 4, 7, 6, 5, 6, 2, 5, 7, 4, 5, 0, 5, 8, 0, 5, 9, 6, 9, 2,
        3, 8, 2, 8, 1, 2, 5, 3, 7, 2, 5, 2, 9, 0, 2, 9, 8, 4, 6, 1, 9, 1, 4, 0, 6, 2, 5, 1, 8, 6,
        2, 6, 4, 5, 1, 4, 9, 2, 3, 0, 9, 5, 7, 0, 3, 1, 2, 5, 9, 3, 1, 3, 2, 2, 5, 7, 4, 6, 1, 5,
        4, 7, 8, 5, 1, 5, 6, 2, 5, 4, 6, 5, 6, 6, 1, 2, 8, 7, 3, 0, 7, 7, 3, 9, 2, 5, 7, 8, 1, 2,
        5, 2, 3, 2, 8, 3, 0, 6, 4, 3, 6, 5, 3, 8, 6, 9, 6, 2, 8, 9, 0, 6, 2, 5, 1, 1, 6, 4, 1, 5,
        3, 2, 1, 8, 2, 6, 9, 3, 4, 8, 1, 4, 4, 5, 3, 1, 2, 5, 5, 8, 2, 0, 7, 6, 6, 0, 9, 1, 3, 4,
        6, 7, 4, 0, 7, 2, 2, 6, 5, 6, 2, 5, 2, 9, 1, 0, 3, 8, 3, 0, 4, 5, 6, 7, 3, 3, 7, 0, 3, 6,
        1, 3, 2, 8, 1, 2, 5, 1, 4, 5, 5, 1, 9, 1, 5, 2, 2, 8, 3, 6, 6, 8, 5, 1, 8, 0, 6, 6, 4, 0,
        6, 2, 5, 7, 2, 7, 5, 9, 5, 7, 6, 1, 4, 1, 8, 3, 4, 2, 5, 9, 0, 3, 3, 2, 0, 3, 1, 2, 5, 3,
        6, 3, 7, 9, 7, 8, 8, 0, 7, 0, 9, 1, 7, 1, 2, 9, 5, 1, 6, 6, 0, 1, 5, 6, 2, 5, 1, 8, 1, 8,
        9, 8, 9, 4, 0, 3, 5, 4, 5, 8, 5, 6, 4, 7, 5, 8, 3, 0, 0, 7, 8, 1, 2, 5, 9, 0, 9, 4, 9, 4,
        7, 0, 1, 7, 7, 2, 9, 2, 8, 2, 3, 7, 9, 1, 5, 0, 3, 9, 0, 6, 2, 5, 4, 5, 4, 7, 4, 7, 3, 5,
        0, 8, 8, 6, 4, 6, 4, 1, 1, 8, 9, 5, 7, 5, 1, 9, 5, 3, 1, 2, 5, 2, 2, 7, 3, 7, 3, 6, 7, 5,
        4, 4, 3, 2, 3, 2, 0, 5, 9, 4, 7, 8, 7, 5, 9, 7, 6, 5, 6, 2, 5, 1, 1, 3, 6, 8, 6, 8, 3, 7,
        7, 2, 1, 6, 1, 6, 0, 2, 9, 7, 3, 9, 3, 7, 9, 8, 8, 2, 8, 1, 2, 5, 5, 6, 8, 4, 3, 4, 1, 8,
        8, 6, 0, 8, 0, 8, 0, 1, 4, 8, 6, 9, 6, 8, 9, 9, 4, 1, 4, 0, 6, 2, 5, 2, 8, 4, 2, 1, 7, 0,
        9, 4, 3, 0, 4, 0, 4, 0, 0, 7, 4, 3, 4, 8, 4, 4, 9, 7, 0, 7, 0, 3, 1, 2, 5, 1, 4, 2, 1, 0,
        8, 5, 4, 7, 1, 5, 2, 0, 2, 0, 0, 3, 7, 1, 7, 4, 2, 2, 4, 8, 5, 3, 5, 1, 5, 6, 2, 5, 7, 1,
        0, 5, 4, 2, 7, 3, 5, 7, 6, 0, 1, 0, 0, 1, 8, 5, 8, 7, 1, 1, 2, 4, 2, 6, 7, 5, 7, 8, 1, 2,
        5, 3, 5, 5, 2, 7, 1, 3, 6, 7, 8, 8, 0, 0, 5, 0, 0, 9, 2, 9, 3, 5, 5, 6, 2, 1, 3, 3, 7, 8,
        9, 0, 6, 2, 5, 1, 7, 7, 6, 3, 5, 6, 8, 3, 9, 4, 0, 0, 2, 5, 0, 4, 6, 4, 6, 7, 7, 8, 1, 0,
        6, 6, 8, 9, 4, 5, 3, 1, 2, 5, 8, 8, 8, 1, 7, 8, 4, 1, 9, 7, 0, 0, 1, 2, 5, 2, 3, 2, 3, 3,
        8, 9, 0, 5, 3, 3, 4, 4, 7, 2, 6, 5, 6, 2, 5, 4, 4, 4, 0, 8, 9, 2, 0, 9, 8, 5, 0, 0, 6, 2,
        6, 1, 6, 1, 6, 9, 4, 5, 2, 6, 6, 7, 2, 3, 6, 3, 2, 8, 1, 2, 5, 2, 2, 2, 0, 4, 4, 6, 0, 4,
        9, 2, 5, 0, 3, 1, 3, 0, 8, 0, 8, 4, 7, 2, 6, 3, 3, 3, 6, 1, 8, 1, 6, 4, 0, 6, 2, 5, 1, 1,
        1, 0, 2, 2, 3, 0, 2, 4, 6, 2, 5, 1, 5, 6, 5, 4, 0, 4, 2, 3, 6, 3, 1, 6, 6, 8, 0, 9, 0, 8,
        2, 0, 3, 1, 2, 5, 5, 5, 5, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5, 7, 8, 2, 7, 0, 2, 1, 1, 8, 1, 5,
        8, 3, 4, 0, 4, 5, 4, 1, 0, 1, 5, 6, 2, 5, 2, 7, 7, 5, 5, 5, 7, 5, 6, 1, 5, 6, 2, 8, 9, 1,
        3, 5, 1, 0, 5, 9, 0, 7, 9, 1, 7, 0, 2, 2, 7, 0, 5, 0, 7, 8, 1, 2, 5, 1, 3, 8, 7, 7, 7, 8,
        7, 8, 0, 7, 8, 1, 4, 4, 5, 6, 7, 5, 5, 2, 9, 5, 3, 9, 5, 8, 5, 1, 1, 3, 5, 2, 5, 3, 9, 0,
        6, 2, 5, 6, 9, 3, 8, 8, 9, 3, 9, 0, 3, 9, 0, 7, 2, 2, 8, 3, 7, 7, 6, 4, 7, 6, 9, 7, 9, 2,
        5, 5, 6, 7, 6, 2, 6, 9, 5, 3, 1, 2, 5, 3, 4, 6, 9, 4, 4, 6, 9, 5, 1, 9, 5, 3, 6, 1, 4, 1,
        8, 8, 8, 2, 3, 8, 4, 8, 9, 6, 2, 7, 8, 3, 8, 1, 3, 4, 7, 6, 5, 6, 2, 5, 1, 7, 3, 4, 7, 2,
        3, 4, 7, 5, 9, 7, 6, 8, 0, 7, 0, 9, 4, 4, 1, 1, 9, 2, 4, 4, 8, 1, 3, 9, 1, 9, 0, 6, 7, 3,
        8, 2, 8, 1, 2, 5, 8, 6, 7, 3, 6, 1, 7, 3, 7, 9, 8, 8, 4, 0, 3, 5, 4, 7, 2, 0, 5, 9, 6, 2,
        2, 4, 0, 6, 9, 5, 9, 5, 3, 3, 6, 9, 1, 4, 0, 6, 2, 5,
    ];

    shift &= 63;
    const xa = TABLE[shift];
    const xb = TABLE[shift + 1];
    const numNewDigits = (xa >> 11);
    const size_t pow5a = (0x7FF & xa);
    const size_t pow5b = (0x7FF & xb);
    const pow5 = TABLE_POW5[pow5a .. $][];
    foreach (i, p5; pow5.enumerate().take(pow5b - pow5a))
    {
        if (i >= d.numDigits)
            return numNewDigits - 1;
        else if (d.digits[i] == p5)
            continue;
        else if (d.digits[i] < p5)
            return numNewDigits - 1;
        else
            return numNewDigits;
    }
    return numNewDigits;
}
