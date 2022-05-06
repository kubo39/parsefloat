module parsefloat.parse;

import std.ascii : isDigit;
import std.exception : enforce;
import std.meta;
import std.range;
import std.traits;

private import std.conv : ConvException;

import parsefloat.number;

enum ulong MIN_19DIGIT_INT = 100_0000_0000_0000_0000;

/// Parse 8 digits, loaded as bytes in little-endian order.
///
/// This uses the trick where every digit is in [0x030, 0x39],
/// and therefore can be parsed in 3 multiplications, much
/// faster than the normal 8.
///
/// This is based off the algorithm described in "Fast numeric string to
/// int", available here: <https://johnnylee-sde.github.io/Fast-numeric-string-to-int/>.
ulong parse8Digits(ulong v)
{
    enum ulong MASK = 0x0000_00FF_0000_00FF;
    enum ulong MUL1 = 0x000F_4240_0000_0064;
    enum ulong MUL2 = 0x0000_2710_0000_0001;
    v -= 0x3030_3030_3030_3030;
    v = (v * 10) + (v >> 8); // will not overflow, fits in 63 bits
    const v1 = (v & MASK) * MUL1;
    const v2 = ((v >> 16) & MASK) * MUL2;
    return cast(ulong) (cast(uint)((v1 + v2) >> 32));
}

/// Parse digits until a non-digit character is found.
void parseDigits(Source)(ref Source source, void delegate(ulong) f)
if (isInputRange!Source &&
    !is(Source == enum))
{
    while (!source.empty)
    {
        int c = source.front;
        if (isDigit(c))
        {
            int i = c - '0';
            f(i);
            source.popFront;
        }
        else
            break;
    }
}

/// Parse digits until a non-digit character is found.
void tryParseDigits(Source)(ref Source source, ref ulong x)
if (isInputRange!Source &&
    !is(Source == enum))
{
    // may cause overflows, to be handled later
    parseDigits(source, (digit) { x = x * 10 + digit; });
}

/// Parse up to 19 digits (the max that can be stored in a 64-bit integer).
void tryParse19Digits(Source)(ref Source source, ref ulong x)
if (isInputRange!Source &&
    !is(Source == enum))
{
    while (x < MIN_19DIGIT_INT)
    {
        if (source.empty)
            break;
        auto i = source.front;
        const d = i - '0';
        if (d < 10)
        {
            x = (x * 10) + d;
            source.popFront;
        }
        else
            break;
    }
}

/// Parse a partial, non-special floating point number.
///
/// This creates a representation of the float as the
/// significant digits and the decimal exponent.
void parsePartialNumber(Source)(ref Source source, ref Number number)
if (isInputRange!Source &&
    !is(Source == enum))
{
    auto start = source;

    // parse initial digits before dot
    ulong mantissa = 0;
    tryParseDigits(source, mantissa);
    auto nDigits = start.length - source.length;

    // Have we seen any mantissa digits so far?
    enforce(nDigits > 0, new ConvException("no digits seen"));

    // handle dot with the following digits
    size_t nAfterDot = 0;
    long exponent = 0;
    const intEnd = source;
    if (!source.empty && source.front == '.')
    {
        number.count++;
        source.popFront;
        const before = source;
        tryParseDigits(source, mantissa);
        nAfterDot = before.length - source.length;
        exponent = -nAfterDot;
    }

    nDigits += nAfterDot;
    number.count += nDigits;

    // handle scientific format
    long expNumber = 0;
    if (!source.empty && (source.front == 'e' || source.front == 'E'))
    {
        char sexp = 0;
        int e = 0;

        source.popFront();
        enforce(!source.empty, new ConvException("Unexpected end of input"));
        switch (source.front)
        {
            case '-':    sexp++;
                         goto case;
            case '+':    number.count++;
                         source.popFront();
                         break;
            default: {}
        }
        bool sawDigits = false;
        while (!source.empty && isDigit(source.front))
        {
            if (e < 0x7FFFFFFF / 10 - 10)   // prevent integer overflow
            {
                e = e * 10 + source.front - '0';
            }
            number.count++;
            source.popFront();
            sawDigits = true;
        }
        exponent += (sexp) ? -e : e;
        enforce(sawDigits, new ConvException("No digits seen."));
    }
    const len = start.length - source.length;

    // handle uncommon case with many digits
    if (nDigits <= 19)
    {
        number.exponent = exponent;
        number.mantissa = mantissa;
        number.manyDigits = false;
        return;
    }

    nDigits -= 19;
    auto manyDigits = false;
    auto p = start;
    while (!p.empty && (p.front == '0' || p.front == '.'))
    {
        // '0' = b'.' + 2
        nDigits -= p.front - ('0' - 1);
        p.popFront();
    }
    if (nDigits > 0)
    {
        // at this point we have more than 19 significant digits, let's try again
        manyDigits = true;
        mantissa = 0;
        auto s = start;
        tryParse19Digits(s, mantissa);
        if (mantissa >= MIN_19DIGIT_INT)
        {
            // big int
            exponent = s.length - intEnd.length;
        }
        else
        {
            // We know this is true because we had more than 19
            // digits previously, so we overflowed a 64-bit integer,
            // but parsing only the integral digits produced less
            // than 19 digits. That means we must have a decimal
            // point, and at least 1 fractional digit.
            s.popFront;
            const before = s;
            tryParse19Digits(s, mantissa);
            exponent = - (before.length - s.length);
        }
        // add back the explicit part
        exponent += expNumber;
    }
    number.exponent = exponent;
    number.mantissa = mantissa;
    number.manyDigits = manyDigits;
    enforce(source.empty, "Failed to parse");
}


/// Try to parse a non-special floating point number.
bool parseNumber(Source)(ref Source source, ref Number number)
if (isInputRange!Source &&
    !is(Source == enum))
{
    parsePartialNumber(source, number);
    return source.empty;
}
