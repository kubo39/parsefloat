module parsefloat.common;

///
struct BiasedFp
{
    /// The significant digit.
    ulong f;
    /// The biased, binary exponent.
    int e;
}
