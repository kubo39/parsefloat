// ported from https://github.com/tiehuis/zig-parsefloat/blob/master/test_all_fxx_data.zig

import std.file;
import std.path;
import std.stdio;

import std.conv;
//import parsefloat;

// f16 f32 f64 string_repr
struct TestCase
{
    uint f32bits;
    ulong f64bits;
    string floatString;
}

void scanLine(string line, ref TestCase testcase)
{
    static import std.conv;
    import std.string : split;

    auto arr = line.split(' ');
    float word1 = std.conv.parse!float(arr[1]);
    testcase.f32bits = *cast(uint*) &word1;
    double word2 = std.conv.parse!double(arr[2]);
    testcase.f64bits = *cast(ulong*) &word2;
    testcase.floatString = arr[3];
}

void main()
{
    string[] fileList = [
        // "../parse-number-fxx-test-data/data/freetype-2-7.txt",
        // "../parse-number-fxx-test-data/data/google-double-conversion.txt",
        // "../parse-number-fxx-test-data/data/google-wuffs.txt",
        // "../parse-number-fxx-test-data/data/ibm-fpgen.txt",
        "../parse-number-fxx-test-data/data/lemire-fast-double-parser.txt",
        // "../parse-number-fxx-test-data/data/more-test-cases.txt",
        // "../parse-number-fxx-test-data/data/remyoudompheng-fptest-0.txt",
        // "../parse-number-fxx-test-data/data/remyoudompheng-fptest-1.txt",
        // "../parse-number-fxx-test-data/data/remyoudompheng-fptest-2.txt",
        // "../parse-number-fxx-test-data/data/remyoudompheng-fptest-3.txt",
        // "../parse-number-fxx-test-data/data/tencent-rapidjson.txt",
        // "../parse-number-fxx-test-data/data/ulfjack-ryu.txt"
        ];

    // pre-open all files to confirm they exist
    const cwd = getcwd();
    foreach (file; fileList)
    {
        scope f = File(buildPath(cwd, file), "r");
        scope(exit) f.close;
    }

    size_t count = 0;
    size_t fail = 0;

    // data format [f16-bits] [f32bits] [f64-bits] [string-to-parse]
    foreach (file; fileList)
    {
        scope f = File(buildPath(cwd, file), "r");
        scope(exit) f.close;

        TestCase tc;
        foreach (line; f.byLineCopy())
        {
            import std.range;
            if (line.empty)
                continue;

            auto failure = false;
            import std.exception;
            try scanLine(line, tc);
            catch (Exception)
            {
                fail++;
                count++;
                continue;
            }

            // f32bits
            string s = tc.floatString;
            double f32result = parse!float(s);
            if (tc.f32bits != f32result)
            {
                // stderr.writefln(" | float: %s, found %f", line, f32result);
                failure = true;
            }

            // f64bits
            s = tc.floatString;
            double f64result = parse!double(s);
            if (tc.f64bits != f64result)
            {
                // stderr.writefln(" | double: %s, found %f", line, f64result);
                failure = true;
            }

            if (failure) fail++;
            count++;
        }
    }
    stderr.writefln("%d/%d succeeded (%d fail)", count - fail, count, fail);
}
