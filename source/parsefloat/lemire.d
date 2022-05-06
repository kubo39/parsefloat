module parsefloat.lemire;

import core.int128;

import parsefloat.common;

/// Compute a float using an extended-precision representation.
///
/// Fast conversion of a the significant digits and decimal exponent
/// a float to an extended representation with a binary float. This
/// algorithm will accurately parse the vast majority of cases,
/// and uses a 128-bit representation (with a fallback 192-bit
/// representation).
///
/// This algorithm scales the exponent by the decimal exponent
/// using pre-computed powers-of-5, and calculates if the
/// representation can be unambiguously rounded to the nearest
/// machine float. Near-halfway cases are not handled here,
/// and are represented by a negative, biased binary exponent.
///
/// The algorithm is described in detail in "Daniel Lemire, Number Parsing
/// at a Gigabyte per Second" in section 5, "Fast Algorithm", and
/// section 6, "Exact Numbers And Ties", available online:
/// <https://arxiv.org/abs/2101.11408.pdf>.
BiasedFp eiselLemire(T)(long q, ulong _w) if (is(T == double) || is(T == float))
{
    static if (is(T == double))
    {
        size_t MANTISSA_EXPLICIT_BITS = 52;
        int MIN_EXPONENT_ROUND_TO_EVEN = -4;
        int MAX_EXPONENT_ROUND_TO_EVEN = 23;
        int MINIMUM_EXPONENT = -1023;
        int INFINITE_POWER = 0x7FF;
        int SMALLEST_POWER_OF_TEN = -342;
        int LARGEST_POWER_OF_TEN = 308;
    }
    else static if (is(T == float))
    {
        size_t MANTISSA_EXPLICIT_BITS = 23;
        int MIN_EXPONENT_ROUND_TO_EVEN = -17;
        int MAX_EXPONENT_ROUND_TO_EVEN = 10;
        int MINIMUM_EXPONENT = -127;
        int INFINITE_POWER = 0xFF;
        int SMALLEST_POWER_OF_TEN = -65;
        int LARGEST_POWER_OF_TEN = 38;
    }

    ulong w = _w;
    BiasedFp fpZero = { f: 0, e: 0 };
    BiasedFp fpInf = { f: 0, e: INFINITE_POWER };
    BiasedFp fpError = { f: 0, e: -1 };

    // Short-circuit if the value can only be a literal 0 or infinity.
    if (w == 0 || q < cast(long) SMALLEST_POWER_OF_TEN)
        return fpZero;
    else if (q > cast(long) LARGEST_POWER_OF_TEN)
        return fpInf;

    // Normalize our significant digits, so the most-significant bit is set.
    const lz = lzcnt(w);
    w <<= lz;
    const r = computeProductApprox(q, w, MANTISSA_EXPLICIT_BITS + 3);
    if (r.lo == 0xFFFF_FFFF_FFFF_FFFF)
    {
        // If we have failed to approximate w x 5^-q with our 128-bit value.
        // Since the addition of 1 could lead to an overflow which could then
        // round up over the half-way point, this can lead to improper rounding
        // of a float.
        //
        // However, this can only occur if q ∈ [-27, 55]. The upper bound of q
        // is 55 because 5^55 < 2^128, however, this can only happen if 5^q > 2^64,
        // since otherwise the product can be represented in 64-bits, producing
        // an exact result. For negative exponents, rounding-to-even can
        // only occur if 5^-q < 2^64.
        //
        // For detailed explanations of rounding for negative exponents, see
        // <https://arxiv.org/pdf/2101.11408.pdf#section.9.1>. For detailed
        // explanations of rounding for positive exponents, see
        // <https://arxiv.org/pdf/2101.11408.pdf#section.8>.
        const insideSafeExponent = (q >= -27) && (q <= 55);
        if (!insideSafeExponent)
            return fpError;
    }
    const upperbit = cast(int) (r.hi >> 63);
    ulong mantissa = r.hi >> (upperbit + 64 - cast(int) MANTISSA_EXPLICIT_BITS - 3);
    int power2 = power(cast(int) q) + upperbit - cast(int) lz - MINIMUM_EXPONENT;
    if (power2 <= 0)
    {
        if (-power2 + 1 >= 64)
        {
            // Have more than 64 bits below the minimum exponent, must be 0.
            return fpZero;
        }
        // Have a subnormal value.
        mantissa >>= -power2 + 1;
        mantissa += mantissa & 1;
        mantissa >>= 1;
        power2 = cast(int) (mantissa >= (1UL << MANTISSA_EXPLICIT_BITS));
        return BiasedFp(mantissa, power2);
    }
    // Need to handle rounding ties. Normally, we need to round up,
    // but if we fall right in between and and we have an even basis, we
    // need to round down.
    //
    // This will only occur if:
    //  1. The lower 64 bits of the 128-bit representation is 0.
    //      IE, 5^q fits in single 64-bit word.
    //  2. The least-significant bit prior to truncated mantissa is odd.
    //  3. All the bits truncated when shifting to mantissa bits + 1 are 0.
    //
    // Or, we may fall between two floats: we are exactly halfway.
    if (r.lo <= 1
        && q >= cast(long) MIN_EXPONENT_ROUND_TO_EVEN
        && q <= cast(long) MAX_EXPONENT_ROUND_TO_EVEN
        && (mantissa & 3) == 1
        && (mantissa << (upperbit + 64 - cast(int) MANTISSA_EXPLICIT_BITS - 3)) == r.hi)
    {
        // Zero the lowest bit, so we don't round up.
        mantissa &= ~1UL;
    }
    // Round-to-even, then shift the significant digits into place.
    mantissa += (mantissa & 1);
    mantissa >>= 1;
    if (mantissa >= (2UL << MANTISSA_EXPLICIT_BITS))
    {
        // Rounding up overflowed, so the carry bit is set. Set the
        // mantissa to 1 (only the implicit, hidden bit is set) and
        // increase the exponent.
        mantissa = 1UL << MANTISSA_EXPLICIT_BITS;
        power2++;
    }
    // Zero out the hidden bit.
    mantissa &= ~(1UL << MANTISSA_EXPLICIT_BITS);
    if (power2 >= INFINITE_POWER)
    {
        // Exponent is above largest normal value, must be infinite.
        return fpInf;
    }
    return BiasedFp(mantissa, power2);
}

private:

/// Calculate a base 2 exponent from a decimal exponent.
/// This uses a pre-computed integer approximation for
/// log2(10), where 217706 / 2^16 is accurate for the
/// entire range of non-finite decimal exponents.
int power(int q)
{
    return (cast(int)(q * (152_170 + 65536)) >> 16) + 63;
}

///
Cent fullMultiplication(ulong _a, ulong _b)
{
    Cent a = { lo: _a, hi: 0 };
    Cent b = { lo: _b, hi: 0 };
    return a.mul(b);
}

// This will compute or rather approximate w * 5**q and return a pair of 64-bit words
// approximating the result, with the "high" part corresponding to the most significant
// bits and the low part corresponding to the least significant bits.
Cent computeProductApprox(long q, long w, size_t precision)
{
    assert(q >= SMALLEST_POWER_OF_FIVE);
    assert(q <= LARGEST_POWER_OF_FIVE);
    assert(precision <= 64);

    const ulong mask = precision < 64
        ? 0xFFFF_FFFF_FFFF_FFFF_UL >> precision
        : 0xFFFF_FFFF_FFFF_FFFF_UL;

    // 5^q < 2^64, then the multiplication always provides an exact value.
    // That means whenever we need to round ties to even, we always have
    // an exact value.
    const index = cast(size_t) (q - cast(long) SMALLEST_POWER_OF_FIVE);
    const pow5 = POWER_OF_FIVE_128[index];
    // Only need one multiplication as long as there is 1 zero but
    // in the explicit mantissa bits, +1 for the hidden bit, +1 to
    // determine the rounding direction, +1 for if the computed
    // product has a leading zero.
    auto first = fullMultiplication(w, pow5.lo);
    if ((first.hi & mask) == mask)
    {
        // Need to do a second multiplication to get better precision
        // for the lower product. This will always be exact
        // where q is < 55, since 5^55 < 2^128. If this wraps,
        // then we need to need to round up the hi product.
        auto second = fullMultiplication(w, pow5.hi);
        first.lo = cast(ulong) (first.lo + second.hi);
        if (second.hi > first.lo)
            first.hi++;
    }
    return first;
}


///
ulong lzcnt(ulong w)
{
    version (LDC)
    {
        import ldc.intrinsics;
        return llvm_ctlz(w);
    }
    else
    {
        import core.bitop;
        return w == 0 ? 64 : 63 - bsr(w);
    }
}

immutable int SMALLEST_POWER_OF_FIVE = -342;
immutable int LARGEST_POWER_OF_FIVE = 308;
immutable size_t N_POWERS_OF_FIVE = LARGEST_POWER_OF_FIVE - SMALLEST_POWER_OF_FIVE + 1;

// Eisel-Lemire tables.
immutable Cent[N_POWERS_OF_FIVE] POWER_OF_FIVE_128 = [
    { lo: 0xeef453d6923bd65a, hi: 0x113faa2906a13b3f }, // 5^-342
    { lo: 0x9558b4661b6565f8, hi: 0x4ac7ca59a424c507 }, // 5^-341
    { lo: 0xbaaee17fa23ebf76, hi: 0x5d79bcf00d2df649 }, // 5^-340
    { lo: 0xe95a99df8ace6f53, hi: 0xf4d82c2c107973dc }, // 5^-339
    { lo: 0x91d8a02bb6c10594, hi: 0x79071b9b8a4be869 }, // 5^-338
    { lo: 0xb64ec836a47146f9, hi: 0x9748e2826cdee284 }, // 5^-337
    { lo: 0xe3e27a444d8d98b7, hi: 0xfd1b1b2308169b25 }, // 5^-336
    { lo: 0x8e6d8c6ab0787f72, hi: 0xfe30f0f5e50e20f7 }, // 5^-335
    { lo: 0xb208ef855c969f4f, hi: 0xbdbd2d335e51a935 }, // 5^-334
    { lo: 0xde8b2b66b3bc4723, hi: 0xad2c788035e61382 }, // 5^-333
    { lo: 0x8b16fb203055ac76, hi: 0x4c3bcb5021afcc31 }, // 5^-332
    { lo: 0xaddcb9e83c6b1793, hi: 0xdf4abe242a1bbf3d }, // 5^-331
    { lo: 0xd953e8624b85dd78, hi: 0xd71d6dad34a2af0d }, // 5^-330
    { lo: 0x87d4713d6f33aa6b, hi: 0x8672648c40e5ad68 }, // 5^-329
    { lo: 0xa9c98d8ccb009506, hi: 0x680efdaf511f18c2 }, // 5^-328
    { lo: 0xd43bf0effdc0ba48, hi: 0x212bd1b2566def2 },  // 5^-327
    { lo: 0x84a57695fe98746d, hi: 0x14bb630f7604b57 },  // 5^-326
    { lo: 0xa5ced43b7e3e9188, hi: 0x419ea3bd35385e2d }, // 5^-325
    { lo: 0xcf42894a5dce35ea, hi: 0x52064cac828675b9 }, // 5^-324
    { lo: 0x818995ce7aa0e1b2, hi: 0x7343efebd1940993 }, // 5^-323
    { lo: 0xa1ebfb4219491a1f, hi: 0x1014ebe6c5f90bf8 }, // 5^-322
    { lo: 0xca66fa129f9b60a6, hi: 0xd41a26e077774ef6 }, // 5^-321
    { lo: 0xfd00b897478238d0, hi: 0x8920b098955522b4 }, // 5^-320
    { lo: 0x9e20735e8cb16382, hi: 0x55b46e5f5d5535b0 }, // 5^-319
    { lo: 0xc5a890362fddbc62, hi: 0xeb2189f734aa831d }, // 5^-318
    { lo: 0xf712b443bbd52b7b, hi: 0xa5e9ec7501d523e4 }, // 5^-317
    { lo: 0x9a6bb0aa55653b2d, hi: 0x47b233c92125366e }, // 5^-316
    { lo: 0xc1069cd4eabe89f8, hi: 0x999ec0bb696e840a }, // 5^-315
    { lo: 0xf148440a256e2c76, hi: 0xc00670ea43ca250d }, // 5^-314
    { lo: 0x96cd2a865764dbca, hi: 0x380406926a5e5728 }, // 5^-313
    { lo: 0xbc807527ed3e12bc, hi: 0xc605083704f5ecf2 }, // 5^-312
    { lo: 0xeba09271e88d976b, hi: 0xf7864a44c633682e }, // 5^-311
    { lo: 0x93445b8731587ea3, hi: 0x7ab3ee6afbe0211d }, // 5^-310
    { lo: 0xb8157268fdae9e4c, hi: 0x5960ea05bad82964 }, // 5^-309
    { lo: 0xe61acf033d1a45df, hi: 0x6fb92487298e33bd }, // 5^-308
    { lo: 0x8fd0c16206306bab, hi: 0xa5d3b6d479f8e056 }, // 5^-307
    { lo: 0xb3c4f1ba87bc8696, hi: 0x8f48a4899877186c }, // 5^-306
    { lo: 0xe0b62e2929aba83c, hi: 0x331acdabfe94de87 }, // 5^-305
    { lo: 0x8c71dcd9ba0b4925, hi: 0x9ff0c08b7f1d0b14 }, // 5^-304
    { lo: 0xaf8e5410288e1b6f, hi: 0x7ecf0ae5ee44dd9 },  // 5^-303
    { lo: 0xdb71e91432b1a24a, hi: 0xc9e82cd9f69d6150 }, // 5^-302
    { lo: 0x892731ac9faf056e, hi: 0xbe311c083a225cd2 }, // 5^-301
    { lo: 0xab70fe17c79ac6ca, hi: 0x6dbd630a48aaf406 }, // 5^-300
    { lo: 0xd64d3d9db981787d, hi: 0x92cbbccdad5b108 },  // 5^-299
    { lo: 0x85f0468293f0eb4e, hi: 0x25bbf56008c58ea5 }, // 5^-298
    { lo: 0xa76c582338ed2621, hi: 0xaf2af2b80af6f24e }, // 5^-297
    { lo: 0xd1476e2c07286faa, hi: 0x1af5af660db4aee1 }, // 5^-296
    { lo: 0x82cca4db847945ca, hi: 0x50d98d9fc890ed4d }, // 5^-295
    { lo: 0xa37fce126597973c, hi: 0xe50ff107bab528a0 }, // 5^-294
    { lo: 0xcc5fc196fefd7d0c, hi: 0x1e53ed49a96272c8 }, // 5^-293
    { lo: 0xff77b1fcbebcdc4f, hi: 0x25e8e89c13bb0f7a }, // 5^-292
    { lo: 0x9faacf3df73609b1, hi: 0x77b191618c54e9ac }, // 5^-291
    { lo: 0xc795830d75038c1d, hi: 0xd59df5b9ef6a2417 }, // 5^-290
    { lo: 0xf97ae3d0d2446f25, hi: 0x4b0573286b44ad1d }, // 5^-289
    { lo: 0x9becce62836ac577, hi: 0x4ee367f9430aec32 }, // 5^-288
    { lo: 0xc2e801fb244576d5, hi: 0x229c41f793cda73f }, // 5^-287
    { lo: 0xf3a20279ed56d48a, hi: 0x6b43527578c1110f }, // 5^-286
    { lo: 0x9845418c345644d6, hi: 0x830a13896b78aaa9 }, // 5^-285
    { lo: 0xbe5691ef416bd60c, hi: 0x23cc986bc656d553 }, // 5^-284
    { lo: 0xedec366b11c6cb8f, hi: 0x2cbfbe86b7ec8aa8 }, // 5^-283
    { lo: 0x94b3a202eb1c3f39, hi: 0x7bf7d71432f3d6a9 }, // 5^-282
    { lo: 0xb9e08a83a5e34f07, hi: 0xdaf5ccd93fb0cc53 }, // 5^-281
    { lo: 0xe858ad248f5c22c9, hi: 0xd1b3400f8f9cff68 }, // 5^-280
    { lo: 0x91376c36d99995be, hi: 0x23100809b9c21fa1 }, // 5^-279
    { lo: 0xb58547448ffffb2d, hi: 0xabd40a0c2832a78a }, // 5^-278
    { lo: 0xe2e69915b3fff9f9, hi: 0x16c90c8f323f516c }, // 5^-277
    { lo: 0x8dd01fad907ffc3b, hi: 0xae3da7d97f6792e3 }, // 5^-276
    { lo: 0xb1442798f49ffb4a, hi: 0x99cd11cfdf41779c }, // 5^-275
    { lo: 0xdd95317f31c7fa1d, hi: 0x40405643d711d583 }, // 5^-274
    { lo: 0x8a7d3eef7f1cfc52, hi: 0x482835ea666b2572 }, // 5^-273
    { lo: 0xad1c8eab5ee43b66, hi: 0xda3243650005eecf }, // 5^-272
    { lo: 0xd863b256369d4a40, hi: 0x90bed43e40076a82 }, // 5^-271
    { lo: 0x873e4f75e2224e68, hi: 0x5a7744a6e804a291 }, // 5^-270
    { lo: 0xa90de3535aaae202, hi: 0x711515d0a205cb36 }, // 5^-269
    { lo: 0xd3515c2831559a83, hi: 0xd5a5b44ca873e03 },  // 5^-268
    { lo: 0x8412d9991ed58091, hi: 0xe858790afe9486c2 }, // 5^-267
    { lo: 0xa5178fff668ae0b6, hi: 0x626e974dbe39a872 }, // 5^-266
    { lo: 0xce5d73ff402d98e3, hi: 0xfb0a3d212dc8128f }, // 5^-265
    { lo: 0x80fa687f881c7f8e, hi: 0x7ce66634bc9d0b99 }, // 5^-264
    { lo: 0xa139029f6a239f72, hi: 0x1c1fffc1ebc44e80 }, // 5^-263
    { lo: 0xc987434744ac874e, hi: 0xa327ffb266b56220 }, // 5^-262
    { lo: 0xfbe9141915d7a922, hi: 0x4bf1ff9f0062baa8 }, // 5^-261
    { lo: 0x9d71ac8fada6c9b5, hi: 0x6f773fc3603db4a9 }, // 5^-260
    { lo: 0xc4ce17b399107c22, hi: 0xcb550fb4384d21d3 }, // 5^-259
    { lo: 0xf6019da07f549b2b, hi: 0x7e2a53a146606a48 }, // 5^-258
    { lo: 0x99c102844f94e0fb, hi: 0x2eda7444cbfc426d }, // 5^-257
    { lo: 0xc0314325637a1939, hi: 0xfa911155fefb5308 }, // 5^-256
    { lo: 0xf03d93eebc589f88, hi: 0x793555ab7eba27ca }, // 5^-255
    { lo: 0x96267c7535b763b5, hi: 0x4bc1558b2f3458de }, // 5^-254
    { lo: 0xbbb01b9283253ca2, hi: 0x9eb1aaedfb016f16 }, // 5^-253
    { lo: 0xea9c227723ee8bcb, hi: 0x465e15a979c1cadc }, // 5^-252
    { lo: 0x92a1958a7675175f, hi: 0xbfacd89ec191ec9 },  // 5^-251
    { lo: 0xb749faed14125d36, hi: 0xcef980ec671f667b }, // 5^-250
    { lo: 0xe51c79a85916f484, hi: 0x82b7e12780e7401a }, // 5^-249
    { lo: 0x8f31cc0937ae58d2, hi: 0xd1b2ecb8b0908810 }, // 5^-248
    { lo: 0xb2fe3f0b8599ef07, hi: 0x861fa7e6dcb4aa15 }, // 5^-247
    { lo: 0xdfbdcece67006ac9, hi: 0x67a791e093e1d49a }, // 5^-246
    { lo: 0x8bd6a141006042bd, hi: 0xe0c8bb2c5c6d24e0 }, // 5^-245
    { lo: 0xaecc49914078536d, hi: 0x58fae9f773886e18 }, // 5^-244
    { lo: 0xda7f5bf590966848, hi: 0xaf39a475506a899e }, // 5^-243
    { lo: 0x888f99797a5e012d, hi: 0x6d8406c952429603 }, // 5^-242
    { lo: 0xaab37fd7d8f58178, hi: 0xc8e5087ba6d33b83 }, // 5^-241
    { lo: 0xd5605fcdcf32e1d6, hi: 0xfb1e4a9a90880a64 }, // 5^-240
    { lo: 0x855c3be0a17fcd26, hi: 0x5cf2eea09a55067f }, // 5^-239
    { lo: 0xa6b34ad8c9dfc06f, hi: 0xf42faa48c0ea481e }, // 5^-238
    { lo: 0xd0601d8efc57b08b, hi: 0xf13b94daf124da26 }, // 5^-237
    { lo: 0x823c12795db6ce57, hi: 0x76c53d08d6b70858 }, // 5^-236
    { lo: 0xa2cb1717b52481ed, hi: 0x54768c4b0c64ca6e }, // 5^-235
    { lo: 0xcb7ddcdda26da268, hi: 0xa9942f5dcf7dfd09 }, // 5^-234
    { lo: 0xfe5d54150b090b02, hi: 0xd3f93b35435d7c4c }, // 5^-233
    { lo: 0x9efa548d26e5a6e1, hi: 0xc47bc5014a1a6daf }, // 5^-232
    { lo: 0xc6b8e9b0709f109a, hi: 0x359ab6419ca1091b }, // 5^-231
    { lo: 0xf867241c8cc6d4c0, hi: 0xc30163d203c94b62 }, // 5^-230
    { lo: 0x9b407691d7fc44f8, hi: 0x79e0de63425dcf1d }, // 5^-229
    { lo: 0xc21094364dfb5636, hi: 0x985915fc12f542e4 }, // 5^-228
    { lo: 0xf294b943e17a2bc4, hi: 0x3e6f5b7b17b2939d }, // 5^-227
    { lo: 0x979cf3ca6cec5b5a, hi: 0xa705992ceecf9c42 }, // 5^-226
    { lo: 0xbd8430bd08277231, hi: 0x50c6ff782a838353 }, // 5^-225
    { lo: 0xece53cec4a314ebd, hi: 0xa4f8bf5635246428 }, // 5^-224
    { lo: 0x940f4613ae5ed136, hi: 0x871b7795e136be99 }, // 5^-223
    { lo: 0xb913179899f68584, hi: 0x28e2557b59846e3f }, // 5^-222
    { lo: 0xe757dd7ec07426e5, hi: 0x331aeada2fe589cf }, // 5^-221
    { lo: 0x9096ea6f3848984f, hi: 0x3ff0d2c85def7621 }, // 5^-220
    { lo: 0xb4bca50b065abe63, hi: 0xfed077a756b53a9 },  // 5^-219
    { lo: 0xe1ebce4dc7f16dfb, hi: 0xd3e8495912c62894 }, // 5^-218
    { lo: 0x8d3360f09cf6e4bd, hi: 0x64712dd7abbbd95c }, // 5^-217
    { lo: 0xb080392cc4349dec, hi: 0xbd8d794d96aacfb3 }, // 5^-216
    { lo: 0xdca04777f541c567, hi: 0xecf0d7a0fc5583a0 }, // 5^-215
    { lo: 0x89e42caaf9491b60, hi: 0xf41686c49db57244 }, // 5^-214
    { lo: 0xac5d37d5b79b6239, hi: 0x311c2875c522ced5 }, // 5^-213
    { lo: 0xd77485cb25823ac7, hi: 0x7d633293366b828b }, // 5^-212
    { lo: 0x86a8d39ef77164bc, hi: 0xae5dff9c02033197 }, // 5^-211
    { lo: 0xa8530886b54dbdeb, hi: 0xd9f57f830283fdfc }, // 5^-210
    { lo: 0xd267caa862a12d66, hi: 0xd072df63c324fd7b }, // 5^-209
    { lo: 0x8380dea93da4bc60, hi: 0x4247cb9e59f71e6d }, // 5^-208
    { lo: 0xa46116538d0deb78, hi: 0x52d9be85f074e608 }, // 5^-207
    { lo: 0xcd795be870516656, hi: 0x67902e276c921f8b }, // 5^-206
    { lo: 0x806bd9714632dff6, hi: 0xba1cd8a3db53b6 },   // 5^-205
    { lo: 0xa086cfcd97bf97f3, hi: 0x80e8a40eccd228a4 }, // 5^-204
    { lo: 0xc8a883c0fdaf7df0, hi: 0x6122cd128006b2cd }, // 5^-203
    { lo: 0xfad2a4b13d1b5d6c, hi: 0x796b805720085f81 }, // 5^-202
    { lo: 0x9cc3a6eec6311a63, hi: 0xcbe3303674053bb0 }, // 5^-201
    { lo: 0xc3f490aa77bd60fc, hi: 0xbedbfc4411068a9c }, // 5^-200
    { lo: 0xf4f1b4d515acb93b, hi: 0xee92fb5515482d44 }, // 5^-199
    { lo: 0x991711052d8bf3c5, hi: 0x751bdd152d4d1c4a }, // 5^-198
    { lo: 0xbf5cd54678eef0b6, hi: 0xd262d45a78a0635d }, // 5^-197
    { lo: 0xef340a98172aace4, hi: 0x86fb897116c87c34 }, // 5^-196
    { lo: 0x9580869f0e7aac0e, hi: 0xd45d35e6ae3d4da0 }, // 5^-195
    { lo: 0xbae0a846d2195712, hi: 0x8974836059cca109 }, // 5^-194
    { lo: 0xe998d258869facd7, hi: 0x2bd1a438703fc94b }, // 5^-193
    { lo: 0x91ff83775423cc06, hi: 0x7b6306a34627ddcf }, // 5^-192
    { lo: 0xb67f6455292cbf08, hi: 0x1a3bc84c17b1d542 }, // 5^-191
    { lo: 0xe41f3d6a7377eeca, hi: 0x20caba5f1d9e4a93 }, // 5^-190
    { lo: 0x8e938662882af53e, hi: 0x547eb47b7282ee9c }, // 5^-189
    { lo: 0xb23867fb2a35b28d, hi: 0xe99e619a4f23aa43 }, // 5^-188
    { lo: 0xdec681f9f4c31f31, hi: 0x6405fa00e2ec94d4 }, // 5^-187
    { lo: 0x8b3c113c38f9f37e, hi: 0xde83bc408dd3dd04 }, // 5^-186
    { lo: 0xae0b158b4738705e, hi: 0x9624ab50b148d445 }, // 5^-185
    { lo: 0xd98ddaee19068c76, hi: 0x3badd624dd9b0957 }, // 5^-184
    { lo: 0x87f8a8d4cfa417c9, hi: 0xe54ca5d70a80e5d6 }, // 5^-183
    { lo: 0xa9f6d30a038d1dbc, hi: 0x5e9fcf4ccd211f4c }, // 5^-182
    { lo: 0xd47487cc8470652b, hi: 0x7647c3200069671f }, // 5^-181
    { lo: 0x84c8d4dfd2c63f3b, hi: 0x29ecd9f40041e073 }, // 5^-180
    { lo: 0xa5fb0a17c777cf09, hi: 0xf468107100525890 }, // 5^-179
    { lo: 0xcf79cc9db955c2cc, hi: 0x7182148d4066eeb4 }, // 5^-178
    { lo: 0x81ac1fe293d599bf, hi: 0xc6f14cd848405530 }, // 5^-177
    { lo: 0xa21727db38cb002f, hi: 0xb8ada00e5a506a7c }, // 5^-176
    { lo: 0xca9cf1d206fdc03b, hi: 0xa6d90811f0e4851c }, // 5^-175
    { lo: 0xfd442e4688bd304a, hi: 0x908f4a166d1da663 }, // 5^-174
    { lo: 0x9e4a9cec15763e2e, hi: 0x9a598e4e043287fe }, // 5^-173
    { lo: 0xc5dd44271ad3cdba, hi: 0x40eff1e1853f29fd }, // 5^-172
    { lo: 0xf7549530e188c128, hi: 0xd12bee59e68ef47c }, // 5^-171
    { lo: 0x9a94dd3e8cf578b9, hi: 0x82bb74f8301958ce }, // 5^-170
    { lo: 0xc13a148e3032d6e7, hi: 0xe36a52363c1faf01 }, // 5^-169
    { lo: 0xf18899b1bc3f8ca1, hi: 0xdc44e6c3cb279ac1 }, // 5^-168
    { lo: 0x96f5600f15a7b7e5, hi: 0x29ab103a5ef8c0b9 }, // 5^-167
    { lo: 0xbcb2b812db11a5de, hi: 0x7415d448f6b6f0e7 }, // 5^-166
    { lo: 0xebdf661791d60f56, hi: 0x111b495b3464ad21 }, // 5^-165
    { lo: 0x936b9fcebb25c995, hi: 0xcab10dd900beec34 }, // 5^-164
    { lo: 0xb84687c269ef3bfb, hi: 0x3d5d514f40eea742 }, // 5^-163
    { lo: 0xe65829b3046b0afa, hi: 0xcb4a5a3112a5112 },  // 5^-162
    { lo: 0x8ff71a0fe2c2e6dc, hi: 0x47f0e785eaba72ab }, // 5^-161
    { lo: 0xb3f4e093db73a093, hi: 0x59ed216765690f56 }, // 5^-160
    { lo: 0xe0f218b8d25088b8, hi: 0x306869c13ec3532c }, // 5^-159
    { lo: 0x8c974f7383725573, hi: 0x1e414218c73a13fb }, // 5^-158
    { lo: 0xafbd2350644eeacf, hi: 0xe5d1929ef90898fa }, // 5^-157
    { lo: 0xdbac6c247d62a583, hi: 0xdf45f746b74abf39 }, // 5^-156
    { lo: 0x894bc396ce5da772, hi: 0x6b8bba8c328eb783 }, // 5^-155
    { lo: 0xab9eb47c81f5114f, hi: 0x66ea92f3f326564 },  // 5^-154
    { lo: 0xd686619ba27255a2, hi: 0xc80a537b0efefebd }, // 5^-153
    { lo: 0x8613fd0145877585, hi: 0xbd06742ce95f5f36 }, // 5^-152
    { lo: 0xa798fc4196e952e7, hi: 0x2c48113823b73704 }, // 5^-151
    { lo: 0xd17f3b51fca3a7a0, hi: 0xf75a15862ca504c5 }, // 5^-150
    { lo: 0x82ef85133de648c4, hi: 0x9a984d73dbe722fb }, // 5^-149
    { lo: 0xa3ab66580d5fdaf5, hi: 0xc13e60d0d2e0ebba }, // 5^-148
    { lo: 0xcc963fee10b7d1b3, hi: 0x318df905079926a8 }, // 5^-147
    { lo: 0xffbbcfe994e5c61f, hi: 0xfdf17746497f7052 }, // 5^-146
    { lo: 0x9fd561f1fd0f9bd3, hi: 0xfeb6ea8bedefa633 }, // 5^-145
    { lo: 0xc7caba6e7c5382c8, hi: 0xfe64a52ee96b8fc0 }, // 5^-144
    { lo: 0xf9bd690a1b68637b, hi: 0x3dfdce7aa3c673b0 }, // 5^-143
    { lo: 0x9c1661a651213e2d, hi: 0x6bea10ca65c084e },  // 5^-142
    { lo: 0xc31bfa0fe5698db8, hi: 0x486e494fcff30a62 }, // 5^-141
    { lo: 0xf3e2f893dec3f126, hi: 0x5a89dba3c3efccfa }, // 5^-140
    { lo: 0x986ddb5c6b3a76b7, hi: 0xf89629465a75e01c }, // 5^-139
    { lo: 0xbe89523386091465, hi: 0xf6bbb397f1135823 }, // 5^-138
    { lo: 0xee2ba6c0678b597f, hi: 0x746aa07ded582e2c }, // 5^-137
    { lo: 0x94db483840b717ef, hi: 0xa8c2a44eb4571cdc }, // 5^-136
    { lo: 0xba121a4650e4ddeb, hi: 0x92f34d62616ce413 }, // 5^-135
    { lo: 0xe896a0d7e51e1566, hi: 0x77b020baf9c81d17 }, // 5^-134
    { lo: 0x915e2486ef32cd60, hi: 0xace1474dc1d122e },  // 5^-133
    { lo: 0xb5b5ada8aaff80b8, hi: 0xd819992132456ba },  // 5^-132
    { lo: 0xe3231912d5bf60e6, hi: 0x10e1fff697ed6c69 }, // 5^-131
    { lo: 0x8df5efabc5979c8f, hi: 0xca8d3ffa1ef463c1 }, // 5^-130
    { lo: 0xb1736b96b6fd83b3, hi: 0xbd308ff8a6b17cb2 }, // 5^-129
    { lo: 0xddd0467c64bce4a0, hi: 0xac7cb3f6d05ddbde }, // 5^-128
    { lo: 0x8aa22c0dbef60ee4, hi: 0x6bcdf07a423aa96b }, // 5^-127
    { lo: 0xad4ab7112eb3929d, hi: 0x86c16c98d2c953c6 }, // 5^-126
    { lo: 0xd89d64d57a607744, hi: 0xe871c7bf077ba8b7 }, // 5^-125
    { lo: 0x87625f056c7c4a8b, hi: 0x11471cd764ad4972 }, // 5^-124
    { lo: 0xa93af6c6c79b5d2d, hi: 0xd598e40d3dd89bcf }, // 5^-123
    { lo: 0xd389b47879823479, hi: 0x4aff1d108d4ec2c3 }, // 5^-122
    { lo: 0x843610cb4bf160cb, hi: 0xcedf722a585139ba }, // 5^-121
    { lo: 0xa54394fe1eedb8fe, hi: 0xc2974eb4ee658828 }, // 5^-120
    { lo: 0xce947a3da6a9273e, hi: 0x733d226229feea32 }, // 5^-119
    { lo: 0x811ccc668829b887, hi: 0x806357d5a3f525f },  // 5^-118
    { lo: 0xa163ff802a3426a8, hi: 0xca07c2dcb0cf26f7 }, // 5^-117
    { lo: 0xc9bcff6034c13052, hi: 0xfc89b393dd02f0b5 }, // 5^-116
    { lo: 0xfc2c3f3841f17c67, hi: 0xbbac2078d443ace2 }, // 5^-115
    { lo: 0x9d9ba7832936edc0, hi: 0xd54b944b84aa4c0d }, // 5^-114
    { lo: 0xc5029163f384a931, hi: 0xa9e795e65d4df11 },  // 5^-113
    { lo: 0xf64335bcf065d37d, hi: 0x4d4617b5ff4a16d5 }, // 5^-112
    { lo: 0x99ea0196163fa42e, hi: 0x504bced1bf8e4e45 }, // 5^-111
    { lo: 0xc06481fb9bcf8d39, hi: 0xe45ec2862f71e1d6 }, // 5^-110
    { lo: 0xf07da27a82c37088, hi: 0x5d767327bb4e5a4c }, // 5^-109
    { lo: 0x964e858c91ba2655, hi: 0x3a6a07f8d510f86f }, // 5^-108
    { lo: 0xbbe226efb628afea, hi: 0x890489f70a55368b }, // 5^-107
    { lo: 0xeadab0aba3b2dbe5, hi: 0x2b45ac74ccea842e }, // 5^-106
    { lo: 0x92c8ae6b464fc96f, hi: 0x3b0b8bc90012929d }, // 5^-105
    { lo: 0xb77ada0617e3bbcb, hi: 0x9ce6ebb40173744 },  // 5^-104
    { lo: 0xe55990879ddcaabd, hi: 0xcc420a6a101d0515 }, // 5^-103
    { lo: 0x8f57fa54c2a9eab6, hi: 0x9fa946824a12232d }, // 5^-102
    { lo: 0xb32df8e9f3546564, hi: 0x47939822dc96abf9 }, // 5^-101
    { lo: 0xdff9772470297ebd, hi: 0x59787e2b93bc56f7 }, // 5^-100
    { lo: 0x8bfbea76c619ef36, hi: 0x57eb4edb3c55b65a }, // 5^-99
    { lo: 0xaefae51477a06b03, hi: 0xede622920b6b23f1 }, // 5^-98
    { lo: 0xdab99e59958885c4, hi: 0xe95fab368e45eced }, // 5^-97
    { lo: 0x88b402f7fd75539b, hi: 0x11dbcb0218ebb414 }, // 5^-96
    { lo: 0xaae103b5fcd2a881, hi: 0xd652bdc29f26a119 }, // 5^-95
    { lo: 0xd59944a37c0752a2, hi: 0x4be76d3346f0495f }, // 5^-94
    { lo: 0x857fcae62d8493a5, hi: 0x6f70a4400c562ddb }, // 5^-93
    { lo: 0xa6dfbd9fb8e5b88e, hi: 0xcb4ccd500f6bb952 }, // 5^-92
    { lo: 0xd097ad07a71f26b2, hi: 0x7e2000a41346a7a7 }, // 5^-91
    { lo: 0x825ecc24c873782f, hi: 0x8ed400668c0c28c8 }, // 5^-90
    { lo: 0xa2f67f2dfa90563b, hi: 0x728900802f0f32fa }, // 5^-89
    { lo: 0xcbb41ef979346bca, hi: 0x4f2b40a03ad2ffb9 }, // 5^-88
    { lo: 0xfea126b7d78186bc, hi: 0xe2f610c84987bfa8 }, // 5^-87
    { lo: 0x9f24b832e6b0f436, hi: 0xdd9ca7d2df4d7c9 },  // 5^-86
    { lo: 0xc6ede63fa05d3143, hi: 0x91503d1c79720dbb }, // 5^-85
    { lo: 0xf8a95fcf88747d94, hi: 0x75a44c6397ce912a }, // 5^-84
    { lo: 0x9b69dbe1b548ce7c, hi: 0xc986afbe3ee11aba }, // 5^-83
    { lo: 0xc24452da229b021b, hi: 0xfbe85badce996168 }, // 5^-82
    { lo: 0xf2d56790ab41c2a2, hi: 0xfae27299423fb9c3 }, // 5^-81
    { lo: 0x97c560ba6b0919a5, hi: 0xdccd879fc967d41a }, // 5^-80
    { lo: 0xbdb6b8e905cb600f, hi: 0x5400e987bbc1c920 }, // 5^-79
    { lo: 0xed246723473e3813, hi: 0x290123e9aab23b68 }, // 5^-78
    { lo: 0x9436c0760c86e30b, hi: 0xf9a0b6720aaf6521 }, // 5^-77
    { lo: 0xb94470938fa89bce, hi: 0xf808e40e8d5b3e69 }, // 5^-76
    { lo: 0xe7958cb87392c2c2, hi: 0xb60b1d1230b20e04 }, // 5^-75
    { lo: 0x90bd77f3483bb9b9, hi: 0xb1c6f22b5e6f48c2 }, // 5^-74
    { lo: 0xb4ecd5f01a4aa828, hi: 0x1e38aeb6360b1af3 }, // 5^-73
    { lo: 0xe2280b6c20dd5232, hi: 0x25c6da63c38de1b0 }, // 5^-72
    { lo: 0x8d590723948a535f, hi: 0x579c487e5a38ad0e }, // 5^-71
    { lo: 0xb0af48ec79ace837, hi: 0x2d835a9df0c6d851 }, // 5^-70
    { lo: 0xdcdb1b2798182244, hi: 0xf8e431456cf88e65 }, // 5^-69
    { lo: 0x8a08f0f8bf0f156b, hi: 0x1b8e9ecb641b58ff }, // 5^-68
    { lo: 0xac8b2d36eed2dac5, hi: 0xe272467e3d222f3f }, // 5^-67
    { lo: 0xd7adf884aa879177, hi: 0x5b0ed81dcc6abb0f }, // 5^-66
    { lo: 0x86ccbb52ea94baea, hi: 0x98e947129fc2b4e9 }, // 5^-65
    { lo: 0xa87fea27a539e9a5, hi: 0x3f2398d747b36224 }, // 5^-64
    { lo: 0xd29fe4b18e88640e, hi: 0x8eec7f0d19a03aad }, // 5^-63
    { lo: 0x83a3eeeef9153e89, hi: 0x1953cf68300424ac }, // 5^-62
    { lo: 0xa48ceaaab75a8e2b, hi: 0x5fa8c3423c052dd7 }, // 5^-61
    { lo: 0xcdb02555653131b6, hi: 0x3792f412cb06794d }, // 5^-60
    { lo: 0x808e17555f3ebf11, hi: 0xe2bbd88bbee40bd0 }, // 5^-59
    { lo: 0xa0b19d2ab70e6ed6, hi: 0x5b6aceaeae9d0ec4 }, // 5^-58
    { lo: 0xc8de047564d20a8b, hi: 0xf245825a5a445275 }, // 5^-57
    { lo: 0xfb158592be068d2e, hi: 0xeed6e2f0f0d56712 }, // 5^-56
    { lo: 0x9ced737bb6c4183d, hi: 0x55464dd69685606b }, // 5^-55
    { lo: 0xc428d05aa4751e4c, hi: 0xaa97e14c3c26b886 }, // 5^-54
    { lo: 0xf53304714d9265df, hi: 0xd53dd99f4b3066a8 }, // 5^-53
    { lo: 0x993fe2c6d07b7fab, hi: 0xe546a8038efe4029 }, // 5^-52
    { lo: 0xbf8fdb78849a5f96, hi: 0xde98520472bdd033 }, // 5^-51
    { lo: 0xef73d256a5c0f77c, hi: 0x963e66858f6d4440 }, // 5^-50
    { lo: 0x95a8637627989aad, hi: 0xdde7001379a44aa8 }, // 5^-49
    { lo: 0xbb127c53b17ec159, hi: 0x5560c018580d5d52 }, // 5^-48
    { lo: 0xe9d71b689dde71af, hi: 0xaab8f01e6e10b4a6 }, // 5^-47
    { lo: 0x9226712162ab070d, hi: 0xcab3961304ca70e8 }, // 5^-46
    { lo: 0xb6b00d69bb55c8d1, hi: 0x3d607b97c5fd0d22 }, // 5^-45
    { lo: 0xe45c10c42a2b3b05, hi: 0x8cb89a7db77c506a }, // 5^-44
    { lo: 0x8eb98a7a9a5b04e3, hi: 0x77f3608e92adb242 }, // 5^-43
    { lo: 0xb267ed1940f1c61c, hi: 0x55f038b237591ed3 }, // 5^-42
    { lo: 0xdf01e85f912e37a3, hi: 0x6b6c46dec52f6688 }, // 5^-41
    { lo: 0x8b61313bbabce2c6, hi: 0x2323ac4b3b3da015 }, // 5^-40
    { lo: 0xae397d8aa96c1b77, hi: 0xabec975e0a0d081a }, // 5^-39
    { lo: 0xd9c7dced53c72255, hi: 0x96e7bd358c904a21 }, // 5^-38
    { lo: 0x881cea14545c7575, hi: 0x7e50d64177da2e54 }, // 5^-37
    { lo: 0xaa242499697392d2, hi: 0xdde50bd1d5d0b9e9 }, // 5^-36
    { lo: 0xd4ad2dbfc3d07787, hi: 0x955e4ec64b44e864 }, // 5^-35
    { lo: 0x84ec3c97da624ab4, hi: 0xbd5af13bef0b113e }, // 5^-34
    { lo: 0xa6274bbdd0fadd61, hi: 0xecb1ad8aeacdd58e }, // 5^-33
    { lo: 0xcfb11ead453994ba, hi: 0x67de18eda5814af2 }, // 5^-32
    { lo: 0x81ceb32c4b43fcf4, hi: 0x80eacf948770ced7 }, // 5^-31
    { lo: 0xa2425ff75e14fc31, hi: 0xa1258379a94d028d }, // 5^-30
    { lo: 0xcad2f7f5359a3b3e, hi: 0x96ee45813a04330 },  // 5^-29
    { lo: 0xfd87b5f28300ca0d, hi: 0x8bca9d6e188853fc }, // 5^-28
    { lo: 0x9e74d1b791e07e48, hi: 0x775ea264cf55347e }, // 5^-27
    { lo: 0xc612062576589dda, hi: 0x95364afe032a819e }, // 5^-26
    { lo: 0xf79687aed3eec551, hi: 0x3a83ddbd83f52205 }, // 5^-25
    { lo: 0x9abe14cd44753b52, hi: 0xc4926a9672793543 }, // 5^-24
    { lo: 0xc16d9a0095928a27, hi: 0x75b7053c0f178294 }, // 5^-23
    { lo: 0xf1c90080baf72cb1, hi: 0x5324c68b12dd6339 }, // 5^-22
    { lo: 0x971da05074da7bee, hi: 0xd3f6fc16ebca5e04 }, // 5^-21
    { lo: 0xbce5086492111aea, hi: 0x88f4bb1ca6bcf585 }, // 5^-20
    { lo: 0xec1e4a7db69561a5, hi: 0x2b31e9e3d06c32e6 }, // 5^-19
    { lo: 0x9392ee8e921d5d07, hi: 0x3aff322e62439fd0 }, // 5^-18
    { lo: 0xb877aa3236a4b449, hi: 0x9befeb9fad487c3 },  // 5^-17
    { lo: 0xe69594bec44de15b, hi: 0x4c2ebe687989a9b4 }, // 5^-16
    { lo: 0x901d7cf73ab0acd9, hi: 0xf9d37014bf60a11 },  // 5^-15
    { lo: 0xb424dc35095cd80f, hi: 0x538484c19ef38c95 }, // 5^-14
    { lo: 0xe12e13424bb40e13, hi: 0x2865a5f206b06fba }, // 5^-13
    { lo: 0x8cbccc096f5088cb, hi: 0xf93f87b7442e45d4 }, // 5^-12
    { lo: 0xafebff0bcb24aafe, hi: 0xf78f69a51539d749 }, // 5^-11
    { lo: 0xdbe6fecebdedd5be, hi: 0xb573440e5a884d1c }, // 5^-10
    { lo: 0x89705f4136b4a597, hi: 0x31680a88f8953031 }, // 5^-9
    { lo: 0xabcc77118461cefc, hi: 0xfdc20d2b36ba7c3e }, // 5^-8
    { lo: 0xd6bf94d5e57a42bc, hi: 0x3d32907604691b4d }, // 5^-7
    { lo: 0x8637bd05af6c69b5, hi: 0xa63f9a49c2c1b110 }, // 5^-6
    { lo: 0xa7c5ac471b478423, hi: 0xfcf80dc33721d54 },  // 5^-5
    { lo: 0xd1b71758e219652b, hi: 0xd3c36113404ea4a9 }, // 5^-4
    { lo: 0x83126e978d4fdf3b, hi: 0x645a1cac083126ea }, // 5^-3
    { lo: 0xa3d70a3d70a3d70a, hi: 0x3d70a3d70a3d70a4 }, // 5^-2
    { lo: 0xcccccccccccccccc, hi: 0xcccccccccccccccd }, // 5^-1
    { lo: 0x8000000000000000, hi: 0x0 },                // 5^0
    { lo: 0xa000000000000000, hi: 0x0 },                // 5^1
    { lo: 0xc800000000000000, hi: 0x0 },                // 5^2
    { lo: 0xfa00000000000000, hi: 0x0 },                // 5^3
    { lo: 0x9c40000000000000, hi: 0x0 },                // 5^4
    { lo: 0xc350000000000000, hi: 0x0 },                // 5^5
    { lo: 0xf424000000000000, hi: 0x0 },                // 5^6
    { lo: 0x9896800000000000, hi: 0x0 },                // 5^7
    { lo: 0xbebc200000000000, hi: 0x0 },                // 5^8
    { lo: 0xee6b280000000000, hi: 0x0 },                // 5^9
    { lo: 0x9502f90000000000, hi: 0x0 },                // 5^10
    { lo: 0xba43b74000000000, hi: 0x0 },                // 5^11
    { lo: 0xe8d4a51000000000, hi: 0x0 },                // 5^12
    { lo: 0x9184e72a00000000, hi: 0x0 },                // 5^13
    { lo: 0xb5e620f480000000, hi: 0x0 },                // 5^14
    { lo: 0xe35fa931a0000000, hi: 0x0 },                // 5^15
    { lo: 0x8e1bc9bf04000000, hi: 0x0 },                // 5^16
    { lo: 0xb1a2bc2ec5000000, hi: 0x0 },                // 5^17
    { lo: 0xde0b6b3a76400000, hi: 0x0 },                // 5^18
    { lo: 0x8ac7230489e80000, hi: 0x0 },                // 5^19
    { lo: 0xad78ebc5ac620000, hi: 0x0 },                // 5^20
    { lo: 0xd8d726b7177a8000, hi: 0x0 },                // 5^21
    { lo: 0x878678326eac9000, hi: 0x0 },                // 5^22
    { lo: 0xa968163f0a57b400, hi: 0x0 },                // 5^23
    { lo: 0xd3c21bcecceda100, hi: 0x0 },                // 5^24
    { lo: 0x84595161401484a0, hi: 0x0 },                // 5^25
    { lo: 0xa56fa5b99019a5c8, hi: 0x0 },                // 5^26
    { lo: 0xcecb8f27f4200f3a, hi: 0x0 },                // 5^27
    { lo: 0x813f3978f8940984, hi: 0x4000000000000000 }, // 5^28
    { lo: 0xa18f07d736b90be5, hi: 0x5000000000000000 }, // 5^29
    { lo: 0xc9f2c9cd04674ede, hi: 0xa400000000000000 }, // 5^30
    { lo: 0xfc6f7c4045812296, hi: 0x4d00000000000000 }, // 5^31
    { lo: 0x9dc5ada82b70b59d, hi: 0xf020000000000000 }, // 5^32
    { lo: 0xc5371912364ce305, hi: 0x6c28000000000000 }, // 5^33
    { lo: 0xf684df56c3e01bc6, hi: 0xc732000000000000 }, // 5^34
    { lo: 0x9a130b963a6c115c, hi: 0x3c7f400000000000 }, // 5^35
    { lo: 0xc097ce7bc90715b3, hi: 0x4b9f100000000000 }, // 5^36
    { lo: 0xf0bdc21abb48db20, hi: 0x1e86d40000000000 }, // 5^37
    { lo: 0x96769950b50d88f4, hi: 0x1314448000000000 }, // 5^38
    { lo: 0xbc143fa4e250eb31, hi: 0x17d955a000000000 }, // 5^39
    { lo: 0xeb194f8e1ae525fd, hi: 0x5dcfab0800000000 }, // 5^40
    { lo: 0x92efd1b8d0cf37be, hi: 0x5aa1cae500000000 }, // 5^41
    { lo: 0xb7abc627050305ad, hi: 0xf14a3d9e40000000 }, // 5^42
    { lo: 0xe596b7b0c643c719, hi: 0x6d9ccd05d0000000 }, // 5^43
    { lo: 0x8f7e32ce7bea5c6f, hi: 0xe4820023a2000000 }, // 5^44
    { lo: 0xb35dbf821ae4f38b, hi: 0xdda2802c8a800000 }, // 5^45
    { lo: 0xe0352f62a19e306e, hi: 0xd50b2037ad200000 }, // 5^46
    { lo: 0x8c213d9da502de45, hi: 0x4526f422cc340000 }, // 5^47
    { lo: 0xaf298d050e4395d6, hi: 0x9670b12b7f410000 }, // 5^48
    { lo: 0xdaf3f04651d47b4c, hi: 0x3c0cdd765f114000 }, // 5^49
    { lo: 0x88d8762bf324cd0f, hi: 0xa5880a69fb6ac800 }, // 5^50
    { lo: 0xab0e93b6efee0053, hi: 0x8eea0d047a457a00 }, // 5^51
    { lo: 0xd5d238a4abe98068, hi: 0x72a4904598d6d880 }, // 5^52
    { lo: 0x85a36366eb71f041, hi: 0x47a6da2b7f864750 }, // 5^53
    { lo: 0xa70c3c40a64e6c51, hi: 0x999090b65f67d924 }, // 5^54
    { lo: 0xd0cf4b50cfe20765, hi: 0xfff4b4e3f741cf6d }, // 5^55
    { lo: 0x82818f1281ed449f, hi: 0xbff8f10e7a8921a4 }, // 5^56
    { lo: 0xa321f2d7226895c7, hi: 0xaff72d52192b6a0d }, // 5^57
    { lo: 0xcbea6f8ceb02bb39, hi: 0x9bf4f8a69f764490 }, // 5^58
    { lo: 0xfee50b7025c36a08, hi: 0x2f236d04753d5b4 },  // 5^59
    { lo: 0x9f4f2726179a2245, hi: 0x1d762422c946590 },  // 5^60
    { lo: 0xc722f0ef9d80aad6, hi: 0x424d3ad2b7b97ef5 }, // 5^61
    { lo: 0xf8ebad2b84e0d58b, hi: 0xd2e0898765a7deb2 }, // 5^62
    { lo: 0x9b934c3b330c8577, hi: 0x63cc55f49f88eb2f }, // 5^63
    { lo: 0xc2781f49ffcfa6d5, hi: 0x3cbf6b71c76b25fb }, // 5^64
    { lo: 0xf316271c7fc3908a, hi: 0x8bef464e3945ef7a }, // 5^65
    { lo: 0x97edd871cfda3a56, hi: 0x97758bf0e3cbb5ac }, // 5^66
    { lo: 0xbde94e8e43d0c8ec, hi: 0x3d52eeed1cbea317 }, // 5^67
    { lo: 0xed63a231d4c4fb27, hi: 0x4ca7aaa863ee4bdd }, // 5^68
    { lo: 0x945e455f24fb1cf8, hi: 0x8fe8caa93e74ef6a }, // 5^69
    { lo: 0xb975d6b6ee39e436, hi: 0xb3e2fd538e122b44 }, // 5^70
    { lo: 0xe7d34c64a9c85d44, hi: 0x60dbbca87196b616 }, // 5^71
    { lo: 0x90e40fbeea1d3a4a, hi: 0xbc8955e946fe31cd }, // 5^72
    { lo: 0xb51d13aea4a488dd, hi: 0x6babab6398bdbe41 }, // 5^73
    { lo: 0xe264589a4dcdab14, hi: 0xc696963c7eed2dd1 }, // 5^74
    { lo: 0x8d7eb76070a08aec, hi: 0xfc1e1de5cf543ca2 }, // 5^75
    { lo: 0xb0de65388cc8ada8, hi: 0x3b25a55f43294bcb }, // 5^76
    { lo: 0xdd15fe86affad912, hi: 0x49ef0eb713f39ebe }, // 5^77
    { lo: 0x8a2dbf142dfcc7ab, hi: 0x6e3569326c784337 }, // 5^78
    { lo: 0xacb92ed9397bf996, hi: 0x49c2c37f07965404 }, // 5^79
    { lo: 0xd7e77a8f87daf7fb, hi: 0xdc33745ec97be906 }, // 5^80
    { lo: 0x86f0ac99b4e8dafd, hi: 0x69a028bb3ded71a3 }, // 5^81
    { lo: 0xa8acd7c0222311bc, hi: 0xc40832ea0d68ce0c }, // 5^82
    { lo: 0xd2d80db02aabd62b, hi: 0xf50a3fa490c30190 }, // 5^83
    { lo: 0x83c7088e1aab65db, hi: 0x792667c6da79e0fa }, // 5^84
    { lo: 0xa4b8cab1a1563f52, hi: 0x577001b891185938 }, // 5^85
    { lo: 0xcde6fd5e09abcf26, hi: 0xed4c0226b55e6f86 }, // 5^86
    { lo: 0x80b05e5ac60b6178, hi: 0x544f8158315b05b4 }, // 5^87
    { lo: 0xa0dc75f1778e39d6, hi: 0x696361ae3db1c721 }, // 5^88
    { lo: 0xc913936dd571c84c, hi: 0x3bc3a19cd1e38e9 },  // 5^89
    { lo: 0xfb5878494ace3a5f, hi: 0x4ab48a04065c723 },  // 5^90
    { lo: 0x9d174b2dcec0e47b, hi: 0x62eb0d64283f9c76 }, // 5^91
    { lo: 0xc45d1df942711d9a, hi: 0x3ba5d0bd324f8394 }, // 5^92
    { lo: 0xf5746577930d6500, hi: 0xca8f44ec7ee36479 }, // 5^93
    { lo: 0x9968bf6abbe85f20, hi: 0x7e998b13cf4e1ecb }, // 5^94
    { lo: 0xbfc2ef456ae276e8, hi: 0x9e3fedd8c321a67e }, // 5^95
    { lo: 0xefb3ab16c59b14a2, hi: 0xc5cfe94ef3ea101e }, // 5^96
    { lo: 0x95d04aee3b80ece5, hi: 0xbba1f1d158724a12 }, // 5^97
    { lo: 0xbb445da9ca61281f, hi: 0x2a8a6e45ae8edc97 }, // 5^98
    { lo: 0xea1575143cf97226, hi: 0xf52d09d71a3293bd }, // 5^99
    { lo: 0x924d692ca61be758, hi: 0x593c2626705f9c56 }, // 5^100
    { lo: 0xb6e0c377cfa2e12e, hi: 0x6f8b2fb00c77836c }, // 5^101
    { lo: 0xe498f455c38b997a, hi: 0xb6dfb9c0f956447 },  // 5^102
    { lo: 0x8edf98b59a373fec, hi: 0x4724bd4189bd5eac }, // 5^103
    { lo: 0xb2977ee300c50fe7, hi: 0x58edec91ec2cb657 }, // 5^104
    { lo: 0xdf3d5e9bc0f653e1, hi: 0x2f2967b66737e3ed }, // 5^105
    { lo: 0x8b865b215899f46c, hi: 0xbd79e0d20082ee74 }, // 5^106
    { lo: 0xae67f1e9aec07187, hi: 0xecd8590680a3aa11 }, // 5^107
    { lo: 0xda01ee641a708de9, hi: 0xe80e6f4820cc9495 }, // 5^108
    { lo: 0x884134fe908658b2, hi: 0x3109058d147fdcdd }, // 5^109
    { lo: 0xaa51823e34a7eede, hi: 0xbd4b46f0599fd415 }, // 5^110
    { lo: 0xd4e5e2cdc1d1ea96, hi: 0x6c9e18ac7007c91a }, // 5^111
    { lo: 0x850fadc09923329e, hi: 0x3e2cf6bc604ddb0 },  // 5^112
    { lo: 0xa6539930bf6bff45, hi: 0x84db8346b786151c }, // 5^113
    { lo: 0xcfe87f7cef46ff16, hi: 0xe612641865679a63 }, // 5^114
    { lo: 0x81f14fae158c5f6e, hi: 0x4fcb7e8f3f60c07e }, // 5^115
    { lo: 0xa26da3999aef7749, hi: 0xe3be5e330f38f09d }, // 5^116
    { lo: 0xcb090c8001ab551c, hi: 0x5cadf5bfd3072cc5 }, // 5^117
    { lo: 0xfdcb4fa002162a63, hi: 0x73d9732fc7c8f7f6 }, // 5^118
    { lo: 0x9e9f11c4014dda7e, hi: 0x2867e7fddcdd9afa }, // 5^119
    { lo: 0xc646d63501a1511d, hi: 0xb281e1fd541501b8 }, // 5^120
    { lo: 0xf7d88bc24209a565, hi: 0x1f225a7ca91a4226 }, // 5^121
    { lo: 0x9ae757596946075f, hi: 0x3375788de9b06958 }, // 5^122
    { lo: 0xc1a12d2fc3978937, hi: 0x52d6b1641c83ae },   // 5^123
    { lo: 0xf209787bb47d6b84, hi: 0xc0678c5dbd23a49a }, // 5^124
    { lo: 0x9745eb4d50ce6332, hi: 0xf840b7ba963646e0 }, // 5^125
    { lo: 0xbd176620a501fbff, hi: 0xb650e5a93bc3d898 }, // 5^126
    { lo: 0xec5d3fa8ce427aff, hi: 0xa3e51f138ab4cebe }, // 5^127
    { lo: 0x93ba47c980e98cdf, hi: 0xc66f336c36b10137 }, // 5^128
    { lo: 0xb8a8d9bbe123f017, hi: 0xb80b0047445d4184 }, // 5^129
    { lo: 0xe6d3102ad96cec1d, hi: 0xa60dc059157491e5 }, // 5^130
    { lo: 0x9043ea1ac7e41392, hi: 0x87c89837ad68db2f }, // 5^131
    { lo: 0xb454e4a179dd1877, hi: 0x29babe4598c311fb }, // 5^132
    { lo: 0xe16a1dc9d8545e94, hi: 0xf4296dd6fef3d67a }, // 5^133
    { lo: 0x8ce2529e2734bb1d, hi: 0x1899e4a65f58660c }, // 5^134
    { lo: 0xb01ae745b101e9e4, hi: 0x5ec05dcff72e7f8f }, // 5^135
    { lo: 0xdc21a1171d42645d, hi: 0x76707543f4fa1f73 }, // 5^136
    { lo: 0x899504ae72497eba, hi: 0x6a06494a791c53a8 }, // 5^137
    { lo: 0xabfa45da0edbde69, hi: 0x487db9d17636892 },  // 5^138
    { lo: 0xd6f8d7509292d603, hi: 0x45a9d2845d3c42b6 }, // 5^139
    { lo: 0x865b86925b9bc5c2, hi: 0xb8a2392ba45a9b2 },  // 5^140
    { lo: 0xa7f26836f282b732, hi: 0x8e6cac7768d7141e }, // 5^141
    { lo: 0xd1ef0244af2364ff, hi: 0x3207d795430cd926 }, // 5^142
    { lo: 0x8335616aed761f1f, hi: 0x7f44e6bd49e807b8 }, // 5^143
    { lo: 0xa402b9c5a8d3a6e7, hi: 0x5f16206c9c6209a6 }, // 5^144
    { lo: 0xcd036837130890a1, hi: 0x36dba887c37a8c0f }, // 5^145
    { lo: 0x802221226be55a64, hi: 0xc2494954da2c9789 }, // 5^146
    { lo: 0xa02aa96b06deb0fd, hi: 0xf2db9baa10b7bd6c }, // 5^147
    { lo: 0xc83553c5c8965d3d, hi: 0x6f92829494e5acc7 }, // 5^148
    { lo: 0xfa42a8b73abbf48c, hi: 0xcb772339ba1f17f9 }, // 5^149
    { lo: 0x9c69a97284b578d7, hi: 0xff2a760414536efb }, // 5^150
    { lo: 0xc38413cf25e2d70d, hi: 0xfef5138519684aba }, // 5^151
    { lo: 0xf46518c2ef5b8cd1, hi: 0x7eb258665fc25d69 }, // 5^152
    { lo: 0x98bf2f79d5993802, hi: 0xef2f773ffbd97a61 }, // 5^153
    { lo: 0xbeeefb584aff8603, hi: 0xaafb550ffacfd8fa }, // 5^154
    { lo: 0xeeaaba2e5dbf6784, hi: 0x95ba2a53f983cf38 }, // 5^155
    { lo: 0x952ab45cfa97a0b2, hi: 0xdd945a747bf26183 }, // 5^156
    { lo: 0xba756174393d88df, hi: 0x94f971119aeef9e4 }, // 5^157
    { lo: 0xe912b9d1478ceb17, hi: 0x7a37cd5601aab85d }, // 5^158
    { lo: 0x91abb422ccb812ee, hi: 0xac62e055c10ab33a }, // 5^159
    { lo: 0xb616a12b7fe617aa, hi: 0x577b986b314d6009 }, // 5^160
    { lo: 0xe39c49765fdf9d94, hi: 0xed5a7e85fda0b80b }, // 5^161
    { lo: 0x8e41ade9fbebc27d, hi: 0x14588f13be847307 }, // 5^162
    { lo: 0xb1d219647ae6b31c, hi: 0x596eb2d8ae258fc8 }, // 5^163
    { lo: 0xde469fbd99a05fe3, hi: 0x6fca5f8ed9aef3bb }, // 5^164
    { lo: 0x8aec23d680043bee, hi: 0x25de7bb9480d5854 }, // 5^165
    { lo: 0xada72ccc20054ae9, hi: 0xaf561aa79a10ae6a }, // 5^166
    { lo: 0xd910f7ff28069da4, hi: 0x1b2ba1518094da04 }, // 5^167
    { lo: 0x87aa9aff79042286, hi: 0x90fb44d2f05d0842 }, // 5^168
    { lo: 0xa99541bf57452b28, hi: 0x353a1607ac744a53 }, // 5^169
    { lo: 0xd3fa922f2d1675f2, hi: 0x42889b8997915ce8 }, // 5^170
    { lo: 0x847c9b5d7c2e09b7, hi: 0x69956135febada11 }, // 5^171
    { lo: 0xa59bc234db398c25, hi: 0x43fab9837e699095 }, // 5^172
    { lo: 0xcf02b2c21207ef2e, hi: 0x94f967e45e03f4bb }, // 5^173
    { lo: 0x8161afb94b44f57d, hi: 0x1d1be0eebac278f5 }, // 5^174
    { lo: 0xa1ba1ba79e1632dc, hi: 0x6462d92a69731732 }, // 5^175
    { lo: 0xca28a291859bbf93, hi: 0x7d7b8f7503cfdcfe }, // 5^176
    { lo: 0xfcb2cb35e702af78, hi: 0x5cda735244c3d43e }, // 5^177
    { lo: 0x9defbf01b061adab, hi: 0x3a0888136afa64a7 }, // 5^178
    { lo: 0xc56baec21c7a1916, hi: 0x88aaa1845b8fdd0 },  // 5^179
    { lo: 0xf6c69a72a3989f5b, hi: 0x8aad549e57273d45 }, // 5^180
    { lo: 0x9a3c2087a63f6399, hi: 0x36ac54e2f678864b }, // 5^181
    { lo: 0xc0cb28a98fcf3c7f, hi: 0x84576a1bb416a7dd }, // 5^182
    { lo: 0xf0fdf2d3f3c30b9f, hi: 0x656d44a2a11c51d5 }, // 5^183
    { lo: 0x969eb7c47859e743, hi: 0x9f644ae5a4b1b325 }, // 5^184
    { lo: 0xbc4665b596706114, hi: 0x873d5d9f0dde1fee }, // 5^185
    { lo: 0xeb57ff22fc0c7959, hi: 0xa90cb506d155a7ea }, // 5^186
    { lo: 0x9316ff75dd87cbd8, hi: 0x9a7f12442d588f2 },  // 5^187
    { lo: 0xb7dcbf5354e9bece, hi: 0xc11ed6d538aeb2f },  // 5^188
    { lo: 0xe5d3ef282a242e81, hi: 0x8f1668c8a86da5fa }, // 5^189
    { lo: 0x8fa475791a569d10, hi: 0xf96e017d694487bc }, // 5^190
    { lo: 0xb38d92d760ec4455, hi: 0x37c981dcc395a9ac }, // 5^191
    { lo: 0xe070f78d3927556a, hi: 0x85bbe253f47b1417 }, // 5^192
    { lo: 0x8c469ab843b89562, hi: 0x93956d7478ccec8e }, // 5^193
    { lo: 0xaf58416654a6babb, hi: 0x387ac8d1970027b2 }, // 5^194
    { lo: 0xdb2e51bfe9d0696a, hi: 0x6997b05fcc0319e },  // 5^195
    { lo: 0x88fcf317f22241e2, hi: 0x441fece3bdf81f03 }, // 5^196
    { lo: 0xab3c2fddeeaad25a, hi: 0xd527e81cad7626c3 }, // 5^197
    { lo: 0xd60b3bd56a5586f1, hi: 0x8a71e223d8d3b074 }, // 5^198
    { lo: 0x85c7056562757456, hi: 0xf6872d5667844e49 }, // 5^199
    { lo: 0xa738c6bebb12d16c, hi: 0xb428f8ac016561db }, // 5^200
    { lo: 0xd106f86e69d785c7, hi: 0xe13336d701beba52 }, // 5^201
    { lo: 0x82a45b450226b39c, hi: 0xecc0024661173473 }, // 5^202
    { lo: 0xa34d721642b06084, hi: 0x27f002d7f95d0190 }, // 5^203
    { lo: 0xcc20ce9bd35c78a5, hi: 0x31ec038df7b441f4 }, // 5^204
    { lo: 0xff290242c83396ce, hi: 0x7e67047175a15271 }, // 5^205
    { lo: 0x9f79a169bd203e41, hi: 0xf0062c6e984d386 },  // 5^206
    { lo: 0xc75809c42c684dd1, hi: 0x52c07b78a3e60868 }, // 5^207
    { lo: 0xf92e0c3537826145, hi: 0xa7709a56ccdf8a82 }, // 5^208
    { lo: 0x9bbcc7a142b17ccb, hi: 0x88a66076400bb691 }, // 5^209
    { lo: 0xc2abf989935ddbfe, hi: 0x6acff893d00ea435 }, // 5^210
    { lo: 0xf356f7ebf83552fe, hi: 0x583f6b8c4124d43 },  // 5^211
    { lo: 0x98165af37b2153de, hi: 0xc3727a337a8b704a }, // 5^212
    { lo: 0xbe1bf1b059e9a8d6, hi: 0x744f18c0592e4c5c }, // 5^213
    { lo: 0xeda2ee1c7064130c, hi: 0x1162def06f79df73 }, // 5^214
    { lo: 0x9485d4d1c63e8be7, hi: 0x8addcb5645ac2ba8 }, // 5^215
    { lo: 0xb9a74a0637ce2ee1, hi: 0x6d953e2bd7173692 }, // 5^216
    { lo: 0xe8111c87c5c1ba99, hi: 0xc8fa8db6ccdd0437 }, // 5^217
    { lo: 0x910ab1d4db9914a0, hi: 0x1d9c9892400a22a2 }, // 5^218
    { lo: 0xb54d5e4a127f59c8, hi: 0x2503beb6d00cab4b }, // 5^219
    { lo: 0xe2a0b5dc971f303a, hi: 0x2e44ae64840fd61d }, // 5^220
    { lo: 0x8da471a9de737e24, hi: 0x5ceaecfed289e5d2 }, // 5^221
    { lo: 0xb10d8e1456105dad, hi: 0x7425a83e872c5f47 }, // 5^222
    { lo: 0xdd50f1996b947518, hi: 0xd12f124e28f77719 }, // 5^223
    { lo: 0x8a5296ffe33cc92f, hi: 0x82bd6b70d99aaa6f }, // 5^224
    { lo: 0xace73cbfdc0bfb7b, hi: 0x636cc64d1001550b }, // 5^225
    { lo: 0xd8210befd30efa5a, hi: 0x3c47f7e05401aa4e }, // 5^226
    { lo: 0x8714a775e3e95c78, hi: 0x65acfaec34810a71 }, // 5^227
    { lo: 0xa8d9d1535ce3b396, hi: 0x7f1839a741a14d0d }, // 5^228
    { lo: 0xd31045a8341ca07c, hi: 0x1ede48111209a050 }, // 5^229
    { lo: 0x83ea2b892091e44d, hi: 0x934aed0aab460432 }, // 5^230
    { lo: 0xa4e4b66b68b65d60, hi: 0xf81da84d5617853f }, // 5^231
    { lo: 0xce1de40642e3f4b9, hi: 0x36251260ab9d668e }, // 5^232
    { lo: 0x80d2ae83e9ce78f3, hi: 0xc1d72b7c6b426019 }, // 5^233
    { lo: 0xa1075a24e4421730, hi: 0xb24cf65b8612f81f }, // 5^234
    { lo: 0xc94930ae1d529cfc, hi: 0xdee033f26797b627 }, // 5^235
    { lo: 0xfb9b7cd9a4a7443c, hi: 0x169840ef017da3b1 }, // 5^236
    { lo: 0x9d412e0806e88aa5, hi: 0x8e1f289560ee864e }, // 5^237
    { lo: 0xc491798a08a2ad4e, hi: 0xf1a6f2bab92a27e2 }, // 5^238
    { lo: 0xf5b5d7ec8acb58a2, hi: 0xae10af696774b1db }, // 5^239
    { lo: 0x9991a6f3d6bf1765, hi: 0xacca6da1e0a8ef29 }, // 5^240
    { lo: 0xbff610b0cc6edd3f, hi: 0x17fd090a58d32af3 }, // 5^241
    { lo: 0xeff394dcff8a948e, hi: 0xddfc4b4cef07f5b0 }, // 5^242
    { lo: 0x95f83d0a1fb69cd9, hi: 0x4abdaf101564f98e }, // 5^243
    { lo: 0xbb764c4ca7a4440f, hi: 0x9d6d1ad41abe37f1 }, // 5^244
    { lo: 0xea53df5fd18d5513, hi: 0x84c86189216dc5ed }, // 5^245
    { lo: 0x92746b9be2f8552c, hi: 0x32fd3cf5b4e49bb4 }, // 5^246
    { lo: 0xb7118682dbb66a77, hi: 0x3fbc8c33221dc2a1 }, // 5^247
    { lo: 0xe4d5e82392a40515, hi: 0xfabaf3feaa5334a },  // 5^248
    { lo: 0x8f05b1163ba6832d, hi: 0x29cb4d87f2a7400e }, // 5^249
    { lo: 0xb2c71d5bca9023f8, hi: 0x743e20e9ef511012 }, // 5^250
    { lo: 0xdf78e4b2bd342cf6, hi: 0x914da9246b255416 }, // 5^251
    { lo: 0x8bab8eefb6409c1a, hi: 0x1ad089b6c2f7548e }, // 5^252
    { lo: 0xae9672aba3d0c320, hi: 0xa184ac2473b529b1 }, // 5^253
    { lo: 0xda3c0f568cc4f3e8, hi: 0xc9e5d72d90a2741e }, // 5^254
    { lo: 0x8865899617fb1871, hi: 0x7e2fa67c7a658892 }, // 5^255
    { lo: 0xaa7eebfb9df9de8d, hi: 0xddbb901b98feeab7 }, // 5^256
    { lo: 0xd51ea6fa85785631, hi: 0x552a74227f3ea565 }, // 5^257
    { lo: 0x8533285c936b35de, hi: 0xd53a88958f87275f }, // 5^258
    { lo: 0xa67ff273b8460356, hi: 0x8a892abaf368f137 }, // 5^259
    { lo: 0xd01fef10a657842c, hi: 0x2d2b7569b0432d85 }, // 5^260
    { lo: 0x8213f56a67f6b29b, hi: 0x9c3b29620e29fc73 }, // 5^261
    { lo: 0xa298f2c501f45f42, hi: 0x8349f3ba91b47b8f }, // 5^262
    { lo: 0xcb3f2f7642717713, hi: 0x241c70a936219a73 }, // 5^263
    { lo: 0xfe0efb53d30dd4d7, hi: 0xed238cd383aa0110 }, // 5^264
    { lo: 0x9ec95d1463e8a506, hi: 0xf4363804324a40aa }, // 5^265
    { lo: 0xc67bb4597ce2ce48, hi: 0xb143c6053edcd0d5 }, // 5^266
    { lo: 0xf81aa16fdc1b81da, hi: 0xdd94b7868e94050a }, // 5^267
    { lo: 0x9b10a4e5e9913128, hi: 0xca7cf2b4191c8326 }, // 5^268
    { lo: 0xc1d4ce1f63f57d72, hi: 0xfd1c2f611f63a3f0 }, // 5^269
    { lo: 0xf24a01a73cf2dccf, hi: 0xbc633b39673c8cec }, // 5^270
    { lo: 0x976e41088617ca01, hi: 0xd5be0503e085d813 }, // 5^271
    { lo: 0xbd49d14aa79dbc82, hi: 0x4b2d8644d8a74e18 }, // 5^272
    { lo: 0xec9c459d51852ba2, hi: 0xddf8e7d60ed1219e }, // 5^273
    { lo: 0x93e1ab8252f33b45, hi: 0xcabb90e5c942b503 }, // 5^274
    { lo: 0xb8da1662e7b00a17, hi: 0x3d6a751f3b936243 }, // 5^275
    { lo: 0xe7109bfba19c0c9d, hi: 0xcc512670a783ad4 },  // 5^276
    { lo: 0x906a617d450187e2, hi: 0x27fb2b80668b24c5 }, // 5^277
    { lo: 0xb484f9dc9641e9da, hi: 0xb1f9f660802dedf6 }, // 5^278
    { lo: 0xe1a63853bbd26451, hi: 0x5e7873f8a0396973 }, // 5^279
    { lo: 0x8d07e33455637eb2, hi: 0xdb0b487b6423e1e8 }, // 5^280
    { lo: 0xb049dc016abc5e5f, hi: 0x91ce1a9a3d2cda62 }, // 5^281
    { lo: 0xdc5c5301c56b75f7, hi: 0x7641a140cc7810fb }, // 5^282
    { lo: 0x89b9b3e11b6329ba, hi: 0xa9e904c87fcb0a9d }, // 5^283
    { lo: 0xac2820d9623bf429, hi: 0x546345fa9fbdcd44 }, // 5^284
    { lo: 0xd732290fbacaf133, hi: 0xa97c177947ad4095 }, // 5^285
    { lo: 0x867f59a9d4bed6c0, hi: 0x49ed8eabcccc485d }, // 5^286
    { lo: 0xa81f301449ee8c70, hi: 0x5c68f256bfff5a74 }, // 5^287
    { lo: 0xd226fc195c6a2f8c, hi: 0x73832eec6fff3111 }, // 5^288
    { lo: 0x83585d8fd9c25db7, hi: 0xc831fd53c5ff7eab }, // 5^289
    { lo: 0xa42e74f3d032f525, hi: 0xba3e7ca8b77f5e55 }, // 5^290
    { lo: 0xcd3a1230c43fb26f, hi: 0x28ce1bd2e55f35eb }, // 5^291
    { lo: 0x80444b5e7aa7cf85, hi: 0x7980d163cf5b81b3 }, // 5^292
    { lo: 0xa0555e361951c366, hi: 0xd7e105bcc332621f }, // 5^293
    { lo: 0xc86ab5c39fa63440, hi: 0x8dd9472bf3fefaa7 }, // 5^294
    { lo: 0xfa856334878fc150, hi: 0xb14f98f6f0feb951 }, // 5^295
    { lo: 0x9c935e00d4b9d8d2, hi: 0x6ed1bf9a569f33d3 }, // 5^296
    { lo: 0xc3b8358109e84f07, hi: 0xa862f80ec4700c8 },  // 5^297
    { lo: 0xf4a642e14c6262c8, hi: 0xcd27bb612758c0fa }, // 5^298
    { lo: 0x98e7e9cccfbd7dbd, hi: 0x8038d51cb897789c }, // 5^299
    { lo: 0xbf21e44003acdd2c, hi: 0xe0470a63e6bd56c3 }, // 5^300
    { lo: 0xeeea5d5004981478, hi: 0x1858ccfce06cac74 }, // 5^301
    { lo: 0x95527a5202df0ccb, hi: 0xf37801e0c43ebc8 },  // 5^302
    { lo: 0xbaa718e68396cffd, hi: 0xd30560258f54e6ba }, // 5^303
    { lo: 0xe950df20247c83fd, hi: 0x47c6b82ef32a2069 }, // 5^304
    { lo: 0x91d28b7416cdd27e, hi: 0x4cdc331d57fa5441 }, // 5^305
    { lo: 0xb6472e511c81471d, hi: 0xe0133fe4adf8e952 }, // 5^306
    { lo: 0xe3d8f9e563a198e5, hi: 0x58180fddd97723a6 }, // 5^307
    { lo: 0x8e679c2f5e44ff8f, hi: 0x570f09eaa7ea7648 }, // 5^308
];
