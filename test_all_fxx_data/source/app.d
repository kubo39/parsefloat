// ported from https://github.com/tiehuis/zig-parsefloat/blob/master/test_all_fxx_data.zig

import std.file;
import std.path;
import std.stdio;
import std.conv : ConvException;

//import std.conv;
import parsefloat;

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
    testcase.f32bits = std.conv.to!uint(arr[1], 16);
    testcase.f64bits = std.conv.parse!ulong(arr[2], 16);
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
            try
            {
                scanLine(line, tc);

                // f32bits
                string s = tc.floatString;
                float f32 = parse!float(s);
                uint f32result = *cast(uint*) &f32;
                if (tc.f32bits != f32result)
                {
                    stderr.writefln(" | float: %s, found %f", line, f32result);
                    failure = true;
                }

                // f64bits
                s = tc.floatString;
                double f64 = parse!double(s);
                ulong f64result = *cast(ulong*) &f64;
                if (tc.f64bits != f64result)
                {
                    stderr.writefln(" | double: %s, found %f", line, f64result);
                    failure = true;
                }
            }
            catch (ConvException)
            {
                stderr.writefln(" | range error: %s", line);
                fail++;
                count++;
                continue;
            }
            catch (Exception)
            {
                fail++;
                count++;
                continue;
            }

            if (failure) fail++;
            count++;
        }
    }
    stderr.writefln("%d/%d succeeded (%d fail)", count - fail, count, fail);
}
