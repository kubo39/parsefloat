module parsefloat;

import std.meta;
import std.range;
import std.traits;
import std.typecons : Flag, Yes, No, tuple;

private import std.conv : ConvException, text;

private import parsefloat.lemire;

/**
 * Parses a character range to a floating point number.
 *
 * Params:
 *     Target = a floating point type
 *     source = the lvalue of the range to _parse
 *     doCount = the flag for deciding to report the number of consumed characters
 *
 * Returns:
 $(UL
 *     $(LI A floating point number of type `Target` if `doCount` is set to `No.doCount`)
 *     $(LI A `tuple` containing a floating point number of·type `Target` and a `size_t`
 *     if `doCount` is set to `Yes.doCount`))
 *
 * Throws:
 *     A $(LREF ConvException) if `source` is empty, if no number could be
 *     parsed, or if an overflow occurred.
 */
auto parse(Target, Source, Flag!"doCount" doCount = No.doCount)(ref Source source)
if (isInputRange!Source &&
    isSomeChar!(ElementType!Source) &&
    !is(Source == enum) &&
    (is(Target == float) || is(Target == double)) &&
    !is(Target == enum))
{
    import std.ascii : isDigit, isAlpha, toLower, toUpper, isHexDigit;
    import std.exception : enforce;

    static if (isNarrowString!Source)
    {
        import std.string : representation;
        scope p = source.representation;
    }
    else
    {
        alias p = source;
    }

    void advanceSource()
    {
        static if (isNarrowString!Source)
            source = source[$ - p.length .. $];
    }

    static immutable real[14] negtab =
        [ 1e-4096L,1e-2048L,1e-1024L,1e-512L,1e-256L,1e-128L,1e-64L,1e-32L,
                1e-16L,1e-8L,1e-4L,1e-2L,1e-1L,1.0L ];
    static immutable real[13] postab =
        [ 1e+4096L,1e+2048L,1e+1024L,1e+512L,1e+256L,1e+128L,1e+64L,1e+32L,
                1e+16L,1e+8L,1e+4L,1e+2L,1e+1L ];

    ConvException bailOut()(string msg = null, string fn = __FILE__, size_t ln = __LINE__)
    {
        if (msg == null)
            msg = "Floating point conversion error";
        return new ConvException(text(msg, " for input \"", source, "\"."), fn, ln);
    }

    enforce(!p.empty, bailOut());

    size_t count = 0;
    bool sign = false;
    switch (p.front)
    {
    case '-':
        sign = true;
        ++count;
        p.popFront();
        enforce(!p.empty, bailOut());
        if (toLower(p.front) == 'i')
            goto case 'i';
        break;
    case '+':
        ++count;
        p.popFront();
        enforce(!p.empty, bailOut());
        break;
    case 'i': case 'I':
        // inf
        ++count;
        p.popFront();
        enforce(!p.empty && toUpper(p.front) == 'N',
               bailOut("error converting input to floating point"));
        ++count;
        p.popFront();
        enforce(!p.empty && toUpper(p.front) == 'F',
               bailOut("error converting input to floating point"));
        // skip past the last 'f'
        ++count;
        p.popFront();
        advanceSource();
        static if (doCount)
        {
            return tuple!("data", "count")(sign ? -Target.infinity : Target.infinity, count);
        }
        else
        {
            return sign ? -Target.infinity : Target.infinity;
        }
    default: {}
    }

    bool isHex = false;
    bool startsWithZero = p.front == '0';
    if (startsWithZero)
    {
        ++count;
        p.popFront();
        if (p.empty)
        {
            advanceSource();
            static if (doCount)
            {
                return tuple!("data", "count")(cast (Target) (sign ? -0.0 : 0.0), count);
            }
            else
            {
                return sign ? -0.0 : 0.0;
            }
        }

        isHex = p.front == 'x' || p.front == 'X';
        if (isHex)
        {
            ++count;
            p.popFront();
        }
    }
    else if (toLower(p.front) == 'n')
    {
        // nan
        ++count;
        p.popFront();
        enforce(!p.empty && toUpper(p.front) == 'A',
               bailOut("error converting input to floating point"));
        ++count;
        p.popFront();
        enforce(!p.empty && toUpper(p.front) == 'N',
               bailOut("error converting input to floating point"));
        // skip past the last 'n'
        ++count;
        p.popFront();
        advanceSource();
        static if (doCount)
        {
            return tuple!("data", "count")(Target.nan, count);
        }
        else
        {
            return typeof(return).nan;
        }
    }

    /*
     * The following algorithm consists of 2 steps:
     * 1) parseDigits processes the textual input into msdec and possibly
     *    lsdec/msscale variables, followed by the exponent parser which sets
     *    exp below.
     *    Hex: input is 0xaaaaa...p+000... where aaaa is the mantissa in hex
     *    and 000 is the exponent in decimal format with base 2.
     *    Decimal: input is 0.00333...p+000... where 0.0033 is the mantissa
     *    in decimal and 000 is the exponent in decimal format with base 10.
     * 2) Convert msdec/lsdec and exp into native real format
     */

    real ldval = 0.0;
    char dot = 0;                        /* if decimal point has been seen */
    int exp = 0;
    ulong msdec = 0, lsdec = 0;
    ulong msscale = 1;
    bool sawDigits;
    ulong nDigits = 0;

    enum { hex, decimal }

    // sets msdec, lsdec/msscale, and sawDigits by parsing the mantissa digits
    void parseDigits(alias FloatFormat)()
    {
        static if (FloatFormat == hex)
        {
            enum uint base = 16;
            enum ulong msscaleMax = 0x1000_0000_0000_0000UL; // largest power of 16 a ulong holds
            enum ubyte expIter = 4; // iterate the base-2 exponent by 4 for every hex digit
            alias checkDigit = isHexDigit;
            /*
             * convert letter to binary representation: First clear bit
             * to convert lower space chars to upperspace, then -('A'-10)
             * converts letter A to 10, letter B to 11, ...
             */
            alias convertDigit = (int x) => isAlpha(x) ? ((x & ~0x20) - ('A' - 10)) : x - '0';
            sawDigits = false;
        }
        else static if (FloatFormat == decimal)
        {
            enum uint base = 10;
            enum ulong msscaleMax = 10_000_000_000_000_000_000UL; // largest power of 10 a ulong holds
            enum ubyte expIter = 1; // iterate the base-10 exponent once for every decimal digit
            alias checkDigit = isDigit;
            alias convertDigit = (int x) => x - '0';
            // Used to enforce that any mantissa digits are present
            sawDigits = startsWithZero;
        }
        else
            static assert(false, "Unrecognized floating-point format used.");

        while (!p.empty)
        {
            int i = p.front;
            while (checkDigit(i))
            {
                sawDigits = true;        /* must have at least 1 digit   */
                nDigits++;

                i = convertDigit(i);

                if (msdec < (ulong.max - base)/base)
                {
                    // For base 16: Y = ... + y3*16^3 + y2*16^2 + y1*16^1 + y0*16^0
                    msdec = msdec * base + i;
                }
                else if (msscale < msscaleMax)
                {
                    lsdec = lsdec * base + i;
                    msscale *= base;
                }
                else
                {
                    exp += expIter;
                }
                exp -= dot;
                ++count;
                p.popFront();
                if (p.empty)
                    break;
                i = p.front;
                if (i == '_')
                {
                    ++count;
                    p.popFront();
                    if (p.empty)
                        break;
                    i = p.front;
                }
            }
            if (i == '.' && !dot)
            {
                ++count;
                p.popFront();
                dot += expIter;
            }
            else
                break;
        }

        // Have we seen any mantissa digits so far?
        enforce(sawDigits, bailOut("no digits seen"));
        static if (FloatFormat == hex)
            enforce(!p.empty && (p.front == 'p' || p.front == 'P'),
                    bailOut("Floating point parsing: exponent is required"));
    }

    if (isHex)
        parseDigits!hex;
    else
        parseDigits!decimal;

    if (isHex || (!p.empty && (p.front == 'e' || p.front == 'E')))
    {
        char sexp = 0;
        int e = 0;

        ++count;
        p.popFront();
        enforce(!p.empty, new ConvException("Unexpected end of input"));
        switch (p.front)
        {
            case '-':    sexp++;
                         goto case;
            case '+':    ++count;
                         p.popFront();
                         break;
            default: {}
        }
        sawDigits = false;
        while (!p.empty && isDigit(p.front))
        {
            if (e < 0x7FFFFFFF / 10 - 10)   // prevent integer overflow
            {
                e = e * 10 + p.front - '0';
            }
            ++count;
            p.popFront();
            sawDigits = true;
        }
        exp += (sexp) ? -e : e;
        enforce(sawDigits, new ConvException("No digits seen."));
    }

    bool manyDigits = nDigits > 19;
    if (!manyDigits)
    {
        Target value;
        bool r = tryFastPath!Target(exp, msdec, value);
        if (r)
        {
            static if (doCount)
            {
                return tuple!("data", "count")(cast(Target) (sign ? -value : value), count);
            }
            else
            {
                return cast(Target) (sign ? -value : value);
            }
        }
    }

    // If significant digits were truncated, then we can have rounding error
    // only if `mantissa + 1` produces a different result. We also avoid
    // redundantly using the Eisel-Lemire algorithm if it was unable to
    // correctly round on the first pass.
    auto fp = eiselLemire!Target(exp, msdec);
    if (manyDigits && fp.e >= 0 && fp != eiselLemire!Target(exp, msdec + 1))
    {
        fp.e = -1;
    }
    // Unable to correctly round the float using the Eisel-Lemire algorithm.
    if (fp.e < 0) {}
    else
    {
        /// Converts a `BiasedFp` to the closest machine float type.
        static if (is(Target == double))
        {
            size_t MANTISSA_EXPLICIT_BITS = 52;
        }
        else static if (is(Target == float))
        {
            size_t MANTISSA_EXPLICIT_BITS = 23;
        }
        auto word = fp.f;
        word |= cast(ulong)(fp.e) << MANTISSA_EXPLICIT_BITS;
        Target f = *cast(Target*) &word;

        static if (doCount)
        {
            return tuple!("data", "count")(cast(Target) (sign ? -f : f), count);
        }
        else
        {
            return cast(Target) (sign ? -f : f);
        }
    }

    ldval = msdec;
    if (msscale != 1)               /* if stuff was accumulated in lsdec */
        ldval = ldval * msscale + lsdec;

    if (isHex)
    {
        import core.math : ldexp;

        // Exponent is power of 2, not power of 10
        ldval = ldexp(ldval, exp);
    }
    else if (ldval)
    {
        uint u = 0;
        int pow = 4096;

        while (exp > 0)
        {
            while (exp >= pow)
            {
                ldval *= postab[u];
                exp -= pow;
            }
            pow >>= 1;
            u++;
        }
        while (exp < 0)
        {
            while (exp <= -pow)
            {
                ldval *= negtab[u];
                enforce(ldval != 0, new ConvException("Range error"));
                exp += pow;
            }
            pow >>= 1;
            u++;
        }
    }

    // if overflow occurred
    enforce(ldval != real.infinity, new ConvException("Range error"));

    advanceSource();
    static if (doCount)
    {
        return tuple!("data", "count")(cast (Target) (sign ? -ldval : ldval), count);
    }
    else
    {
        return cast (Target) (sign ? -ldval : ldval);
    }
}

private:

/// Detect if the float can be accurately reconstructed from native floats.
bool isFastPath(Target)(long exp, ulong mantissa)
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
    return MIN_EXPONENT_FAST_PATH <= exp
        && exp <= MAX_EXPONENT_DISGUISED_FAST_PATH
        && mantissa <= MAX_MANTISSA_FAST_PATH;
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
bool tryFastPath(Target)(long exp, ulong _mantissa, ref Target value)
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

    if (!isFastPath!(Target)(exp, _mantissa))
        return false;

    if (exp <= MAX_EXPONENT_FAST_PATH)
    {
        // normal fast path
        assert(_mantissa <= MAX_MANTISSA_FAST_PATH);
        value = cast(Target) _mantissa;
        if (exp < 0)
            value = value / pow10FastPath!Target(-exp);
        else
            value = value * pow10FastPath!Target(exp);
    }
    else
    {
        // disguised fast path
        const shift = exp - MAX_EXPONENT_FAST_PATH;
        const mantissa = _mantissa * INT_POW10[shift];
        if (mantissa > MAX_MANTISSA_FAST_PATH)
            return false;
        value = cast(Target) mantissa * pow10FastPath!Target(MAX_EXPONENT_FAST_PATH);
    }
    return true;
}

T biasedFpToFloat(T)(BiasedFp x) if (is(T == float) || is(T == double))
{
    static if (is(T == float))
    {
        size_t MANTISSA_EXPLICIT_BITS = 23;
    }
    else static if (is(T == double))
    {
        size_t MANTISSA_EXPLICIT_BITS = 52;
    }
    auto word = x.f;
    word |= x.e << MANTISSA_EXPLICIT_BITS;
    return *cast(T*) &word;
}


///
unittest
{
    import std.math.operations : isClose;
    import std.math.traits : isNaN, isInfinity;
    import std.typecons : Flag, Yes, No;
    auto str = "123.456";
    auto x = parse!double(str);
    assert(x.isClose(123.456));
    auto str2 = "123.456";
    assert(parse!(double, string, No.doCount)(str2).isClose(123.456));
    auto str3 = "123.456";
    auto r = parse!(double, string, Yes.doCount)(str3);
    assert(r.data.isClose(123.456));
    assert(r.count == 7);
    auto str4 = "-123.456";
    r = parse!(double, string, Yes.doCount)(str4);
    assert(r.data.isClose(-123.456));
    assert(r.count == 8);
    auto str5 = "+123.456";
    r = parse!(double, string, Yes.doCount)(str5);
    assert(r.data.isClose(123.456));
    assert(r.count == 8);
    auto str6 = "inf0";
    r = parse!(double, string, Yes.doCount)(str6);
    assert(isInfinity(r.data) && r.count == 3 && str6 == "0");
    auto str7 = "-0";
    auto r2 = parse!(float, string, Yes.doCount)(str7);
    assert(r2.data.isClose(0.0) && r2.count == 2);
    auto str8 = "nan";
    // auto r3 = parse!(real, string, Yes.doCount)(str8);
    // assert(isNaN(r3.data) && r3.count == 3);
}

/+
unittest
{
    import std.exception;
    import std.math.traits : isNaN, isInfinity;
    import std.math.algebraic : fabs;

    // Compare reals with given precision
    bool feq(in real rx, in real ry, in real precision = 0.000001L)
    {
        if (rx == ry)
            return 1;

        if (isNaN(rx))
            return cast(bool) isNaN(ry);

        if (isNaN(ry))
            return 0;

        return cast(bool)(fabs(rx - ry) <= precision);
    }

    // Make given typed literal
    F Literal(F)(F f)
    {
        return f;
    }

    static foreach (Float; AliasSeq!(float, double, real))
    {
        assert(to!Float("123") == Literal!Float(123));
        assert(to!Float("+123") == Literal!Float(+123));
        assert(to!Float("-123") == Literal!Float(-123));
        assert(to!Float("123e2") == Literal!Float(123e2));
        assert(to!Float("123e+2") == Literal!Float(123e+2));
        assert(to!Float("123e-2") == Literal!Float(123e-2L));
        assert(to!Float("123.") == Literal!Float(123.0));
        assert(to!Float(".375") == Literal!Float(.375));

        assert(to!Float("1.23375E+2") == Literal!Float(1.23375E+2));

        assert(to!Float("0") is 0.0);
        assert(to!Float("-0") is -0.0);

        assert(isNaN(to!Float("nan")));

        assertThrown!ConvException(to!Float("\x00"));
    }

    // min and max
    float f = to!float("1.17549e-38");
    assert(feq(cast(real) f, cast(real) 1.17549e-38));
    assert(feq(cast(real) f, cast(real) float.min_normal));
    f = to!float("3.40282e+38");
    assert(to!string(f) == to!string(3.40282e+38));

    // min and max
    double d = to!double("2.22508e-308");
    assert(feq(cast(real) d, cast(real) 2.22508e-308));
    assert(feq(cast(real) d, cast(real) double.min_normal));
    d = to!double("1.79769e+308");
    assert(to!string(d) == to!string(1.79769e+308));
    assert(to!string(d) == to!string(double.max));

    auto z = real.max / 2L;
    static assert(is(typeof(z) == real));
    assert(!isNaN(z));
    assert(!isInfinity(z));
    string a = to!string(z);
    real b = to!real(a);
    string c = to!string(b);

    assert(c == a, "\n" ~ c ~ "\n" ~ a);

    assert(to!string(to!real(to!string(real.max / 2L))) == to!string(real.max / 2L));

    // min and max
    real r = to!real(to!string(real.min_normal));
    version (NetBSD)
    {
        // NetBSD notice
        // to!string returns 3.3621e-4932L. It is less than real.min_normal and it is subnormal value
        // Simple C code
        //     long double rd = 3.3621e-4932L;
        //     printf("%Le\n", rd);
        // has unexpected result: 1.681050e-4932
        //
        // Bug report: http://gnats.netbsd.org/cgi-bin/query-pr-single.pl?number=50937
    }
    else
    {
        assert(to!string(r) == to!string(real.min_normal));
    }
    r = to!real(to!string(real.max));
    assert(to!string(r) == to!string(real.max));

    real pi = 3.1415926535897932384626433832795028841971693993751L;
    string fullPrecision = "3.1415926535897932384626433832795028841971693993751";
    assert(feq(parse!real(fullPrecision), pi, 2*real.epsilon));
    string fullPrecision2 = "3.1415926535897932384626433832795028841971693993751";
    assert(feq(parse!(real, string, No.doCount)(fullPrecision2), pi, 2*real.epsilon));
    string fullPrecision3= "3.1415926535897932384626433832795028841971693993751";
    auto len = fullPrecision3.length;
    auto res = parse!(real, string, Yes.doCount)(fullPrecision3);
    assert(feq(res.data, pi, 2*real.epsilon));
    assert(res.count == len);

    real x = 0x1.FAFAFAFAFAFAFAFAFAFAFAFAFAFAFAFAAFAAFAFAFAFAFAFAFAP-252L;
    string full = "0x1.FAFAFAFAFAFAFAFAFAFAFAFAFAFAFAFAAFAAFAFAFAFAFAFAFAP-252";
    assert(parse!real(full) == x);
    string full2 = "0x1.FAFAFAFAFAFAFAFAFAFAFAFAFAFAFAFAAFAAFAFAFAFAFAFAFAP-252";
    assert(parse!(real, string, No.doCount)(full2) == x);
    string full3 = "0x1.FAFAFAFAFAFAFAFAFAFAFAFAFAFAFAFAAFAAFAFAFAFAFAFAFAP-252";
    auto len2 = full3.length;
    assert(parse!(real, string, Yes.doCount)(full3) == tuple(x, len2));
}

// Tests for the double implementation
@system unittest
{
    // @system because strtod is not @safe.
    import std.math : floatTraits, RealFormat;

    static if (floatTraits!real.realFormat == RealFormat.ieeeDouble)
    {
        import core.stdc.stdlib, std.exception, std.math;

        //Should be parsed exactly: 53 bit mantissa
        string s = "0x1A_BCDE_F012_3456p10";
        auto x = parse!real(s);
        assert(x == 0x1A_BCDE_F012_3456p10L);
        //1 bit is implicit
        assert(((*cast(ulong*)&x) & 0x000F_FFFF_FFFF_FFFF) == 0xA_BCDE_F012_3456);
        assert(strtod("0x1ABCDEF0123456p10", null) == x);

        s = "0x1A_BCDE_F012_3456p10";
        auto len = s.length;
        assert(parse!(real, string, Yes.doCount)(s) == tuple(x, len));

        //Should be parsed exactly: 10 bit mantissa
        s = "0x3FFp10";
        x = parse!real(s);
        assert(x == 0x03FFp10);
        //1 bit is implicit
        assert(((*cast(ulong*)&x) & 0x000F_FFFF_FFFF_FFFF) == 0x000F_F800_0000_0000);
        assert(strtod("0x3FFp10", null) == x);

        //60 bit mantissa, round up
        s = "0xFFF_FFFF_FFFF_FFFFp10";
        x = parse!real(s);
        assert(isClose(x, 0xFFF_FFFF_FFFF_FFFFp10));
        //1 bit is implicit
        assert(((*cast(ulong*)&x) & 0x000F_FFFF_FFFF_FFFF) == 0x0000_0000_0000_0000);
        assert(strtod("0xFFFFFFFFFFFFFFFp10", null) == x);

        //60 bit mantissa, round down
        s = "0xFFF_FFFF_FFFF_FF90p10";
        x = parse!real(s);
        assert(isClose(x, 0xFFF_FFFF_FFFF_FF90p10));
        //1 bit is implicit
        assert(((*cast(ulong*)&x) & 0x000F_FFFF_FFFF_FFFF) == 0x000F_FFFF_FFFF_FFFF);
        assert(strtod("0xFFFFFFFFFFFFF90p10", null) == x);

        //61 bit mantissa, round up 2
        s = "0x1F0F_FFFF_FFFF_FFFFp10";
        x = parse!real(s);
        assert(isClose(x, 0x1F0F_FFFF_FFFF_FFFFp10));
        //1 bit is implicit
        assert(((*cast(ulong*)&x) & 0x000F_FFFF_FFFF_FFFF) == 0x000F_1000_0000_0000);
        assert(strtod("0x1F0FFFFFFFFFFFFFp10", null) == x);

        //61 bit mantissa, round down 2
        s = "0x1F0F_FFFF_FFFF_FF10p10";
        x = parse!real(s);
        assert(isClose(x, 0x1F0F_FFFF_FFFF_FF10p10));
        //1 bit is implicit
        assert(((*cast(ulong*)&x) & 0x000F_FFFF_FFFF_FFFF) == 0x000F_0FFF_FFFF_FFFF);
        assert(strtod("0x1F0FFFFFFFFFFF10p10", null) == x);

        //Huge exponent
        s = "0x1F_FFFF_FFFF_FFFFp900";
        x = parse!real(s);
        assert(strtod("0x1FFFFFFFFFFFFFp900", null) == x);

        //exponent too big -> converror
        s = "";
        assertThrown!ConvException(x = parse!real(s));
        assert(strtod("0x1FFFFFFFFFFFFFp1024", null) == real.infinity);

        //-exponent too big -> 0
        s = "0x1FFFFFFFFFFFFFp-2000";
        x = parse!real(s);
        assert(x == 0);
        assert(strtod("0x1FFFFFFFFFFFFFp-2000", null) == x);

        s = "0x1FFFFFFFFFFFFFp-2000";
        len = s.length;
        assert(parse!(real, string, Yes.doCount)(s) == tuple(x, len));
    }
}

@system unittest
{
    import core.stdc.errno;
    import core.stdc.stdlib;
    import std.math : floatTraits, RealFormat;

    errno = 0;  // In case it was set by another unittest in a different module.
    struct longdouble
    {
        static if (floatTraits!real.realFormat == RealFormat.ieeeQuadruple)
        {
            ushort[8] value;
        }
        else static if (floatTraits!real.realFormat == RealFormat.ieeeExtended ||
                        floatTraits!real.realFormat == RealFormat.ieeeExtended53)
        {
            ushort[5] value;
        }
        else static if (floatTraits!real.realFormat == RealFormat.ieeeDouble)
        {
            ushort[4] value;
        }
        else
            static assert(false, "Not implemented");
    }

    real ld;
    longdouble x;
    real ld1;
    longdouble x1;
    int i;

    static if (floatTraits!real.realFormat == RealFormat.ieeeQuadruple)
        enum s = "0x1.FFFFFFFFFFFFFFFFFFFFFFFFFFFFp-16382";
    else static if (floatTraits!real.realFormat == RealFormat.ieeeExtended)
        enum s = "0x1.FFFFFFFFFFFFFFFEp-16382";
    else static if (floatTraits!real.realFormat == RealFormat.ieeeExtended53)
        enum s = "0x1.FFFFFFFFFFFFFFFEp-16382";
    else static if (floatTraits!real.realFormat == RealFormat.ieeeDouble)
        enum s = "0x1.FFFFFFFFFFFFFFFEp-1000";
    else
        static assert(false, "Floating point format for real not supported");

    auto s2 = s.idup;
    ld = parse!real(s2);
    assert(s2.empty);
    x = *cast(longdouble *)&ld;

    static if (floatTraits!real.realFormat == RealFormat.ieeeExtended)
    {
        version (CRuntime_Microsoft)
            ld1 = 0x1.FFFFFFFFFFFFFFFEp-16382L; // strtold currently mapped to strtod
        else
            ld1 = strtold(s.ptr, null);
    }
    else static if (floatTraits!real.realFormat == RealFormat.ieeeExtended53)
        ld1 = 0x1.FFFFFFFFFFFFFFFEp-16382L; // strtold rounds to 53 bits.
    else
        ld1 = strtold(s.ptr, null);

    x1 = *cast(longdouble *)&ld1;
    assert(x1 == x && ld1 == ld);

    assert(!errno);

    s2 = "1.0e5";
    ld = parse!real(s2);
    assert(s2.empty);
    x = *cast(longdouble *)&ld;
    ld1 = strtold("1.0e5", null);
    x1 = *cast(longdouble *)&ld1;
}

unittest
{
    import std.exception;

    // https://issues.dlang.org/show_bug.cgi?id=4959
    {
        auto s = "0 ";
        auto x = parse!double(s);
        assert(s == " ");
        assert(x == 0.0);
    }
    {
        auto s = "0 ";
        auto x = parse!(double, string, Yes.doCount)(s);
        assert(s == " ");
        assert(x == tuple(0.0, 1));
    }

    // https://issues.dlang.org/show_bug.cgi?id=3369
    assert(to!float("inf") == float.infinity);
    assert(to!float("-inf") == -float.infinity);

    // https://issues.dlang.org/show_bug.cgi?id=6160
    assert(6_5.536e3L == to!real("6_5.536e3"));                     // 2^16
    assert(0x1000_000_000_p10 == to!real("0x1000_000_000_p10"));    // 7.03687e+13

    // https://issues.dlang.org/show_bug.cgi?id=6258
    assertThrown!ConvException(to!real("-"));
    assertThrown!ConvException(to!real("in"));

    // https://issues.dlang.org/show_bug.cgi?id=7055
    assertThrown!ConvException(to!float("INF2"));

    //extra stress testing
    auto ssOK    = ["1.", "1.1.1", "1.e5", "2e1e", "2a", "2e1_1", "3.4_",
                    "inf", "-inf", "infa", "-infa", "inf2e2", "-inf2e2",
                    "nan", "-NAN", "+NaN", "-nAna", "NAn2e2", "-naN2e2"];
    auto ssKO    = ["", " ", "2e", "2e+", "2e-", "2ee", "2e++1", "2e--1", "2e_1",
                    "+inf", "-in", "I", "+N", "-NaD", "0x3.F"];
    foreach (s; ssOK)
        parse!double(s);
    foreach (s; ssKO)
        assertThrown!ConvException(parse!double(s));
}
+/
