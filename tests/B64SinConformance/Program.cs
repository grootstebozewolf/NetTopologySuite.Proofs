// S3-S10 conformance harness, C# side: replays the shared contract corpus
// (tests/B64SinConformance/corpus.py: DIR/<MODE>.in and the extracted
// oracle's answers DIR/<MODE>.out) against the C# ports of B64Sin.cs and
// compares output BITS and decisions.  The Java port replays the same
// files (java/nts/proofs/numerics/Conformance.java), so bug=0 on both
// means extracted oracle == C# == Java, bit for bit.
// Usage: dotnet run --project tests/B64SinConformance -c Release -- DIR
//        Exit 0 = every mode bit-identical.
// AI assistance disclosure: AI-drafted; human review pending.
using System.Globalization;
using NTS.Proofs.Numerics;

static string H(double v) => unchecked((ulong)BitConverter.DoubleToInt64Bits(v)).ToString("x16");
static double D(string h) => BitConverter.Int64BitsToDouble(unchecked((long)ulong.Parse(h, NumberStyles.HexNumber)));

if (args.Length < 1)
{
    Console.Error.WriteLine("usage: dotnet run --project tests/B64SinConformance -c Release -- CORPUS_DIR");
    return 2;
}
string dir = args[0];

var modes = new (string Mode, Func<string[], string> Eval)[]
{
    ("B64_SIN", f => { double x = D(f[0]); return B64Sin.Accept(x) ? H(B64Sin.Sin(x)) : "DECLINE"; }),
    ("B64_COS", f => { double x = D(f[0]); return B64Sin.Accept(x) ? H(B64Sin.Cos(x)) : "DECLINE"; }),
    ("B64_ARC_PT", f =>
    {
        double cx = D(f[0]), cy = D(f[1]), r = D(f[2]), t = D(f[3]);
        return B64Sin.ArcAccept(cx, cy, r, t) ? H(B64Sin.ArcX(cx, r, t)) + " " + H(B64Sin.ArcY(cy, r, t)) : "DECLINE";
    }),
    ("B64_FRESNEL", f =>
    {
        double x = D(f[0]);
        return B64Sin.FresnelAccept(x) ? H(B64Sin.FresnelC(x)) + " " + H(B64Sin.FresnelS(x)) : "DECLINE_FRESNEL_RANGE";
    }),
    ("B64_CLOTHOID", f =>
    {
        double a = D(f[0]), s = D(f[1]); bool neg = f[2] == "1";
        return B64Sin.ClothoidAccept(a, s)
            ? H(B64Sin.ClothoidIcos(a, s)) + " " + H(B64Sin.ClothoidIsin(neg, a, s)) : "DECLINE_FRESNEL_RANGE";
    }),
    ("B64_SEG_G", f => B64Sin.SegGOutcome(D(f[0]))),
};

int totalBug = 0;
foreach (var (mode, eval) in modes)
{
    var ins = File.ReadAllLines(Path.Combine(dir, mode + ".in")).Where(l => l.Length > 0).ToArray();
    var outs = File.ReadAllLines(Path.Combine(dir, mode + ".out")).Where(l => l.Length > 0).ToArray();
    int ok = 0, bug = 0, declined = 0;
    if (ins.Length != outs.Length)
    {
        Console.WriteLine($"!! {mode}: {ins.Length} inputs but {outs.Length} oracle answers");
        bug = 1;
    }
    else
        for (int i = 0; i < ins.Length; i++)
        {
            string mine = eval(ins[i].Split(' '));
            string theirs = outs[i].Trim();
            if (mine == theirs) { ok++; if (mine.StartsWith("DECLINE")) declined++; }
            else if (++bug <= 10)
                Console.WriteLine($"!! {mode} in=[{ins[i]}] csharp={mine} oracle={theirs}");
        }
    Console.WriteLine($"# {mode} cases {ins.Length}, of which declined {declined}");
    Console.WriteLine($"SUMMARY {mode} ok={ok} warn=0 bug={bug}");
    totalBug += bug;
}
return totalBug == 0 ? 0 : 1;
