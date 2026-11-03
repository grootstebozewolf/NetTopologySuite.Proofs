// S3/S4/S5 conformance harness: C# B64Sin.Sin / Cos / ArcX / ArcY vs the
// Rocq-extracted oracle (modes B64_SIN, B64_COS, B64_ARC_PT), compared on
// output BITS.  Corpus: seeded uniform inputs on [-10, 10],
// random bit patterns in the accepted range (all binades, subnormals),
// thresholds / caps / multiples of pi +-4 ulp, signed zeros, and rejected
// inputs (NaN, infinities, just outside the cap) for DECLINE parity.
// Usage: dotnet run --project tests/B64SinConformance [-- ORACLE_BIN]
//        (default: $ORACLE or oracle/oracle_bin).  Exit 0 = bit-identical.
// AI assistance disclosure: AI-drafted; human review pending.
using System.Diagnostics;
using NTS.Proofs.Numerics;

static ulong Bits(double v) => unchecked((ulong)BitConverter.DoubleToInt64Bits(v));
static double FromBits(ulong b) => BitConverter.Int64BitsToDouble(unchecked((long)b));

var oracle = args.Length > 0 ? args[0]
           : Environment.GetEnvironmentVariable("ORACLE") ?? "oracle/oracle_bin";

var corpus = new List<double>();
var rng = new Random(20261103);
for (int i = 0; i < 200_000; i++) corpus.Add(rng.NextDouble() * 20.0 - 10.0);
var buf = new byte[8];
int kept = 0;
while (kept < 100_000)
{
    rng.NextBytes(buf);
    double v = FromBits(BitConverter.ToUInt64(buf, 0));
    if (double.IsFinite(v) && Math.Abs(v) <= 10.0) { corpus.Add(v); kept++; }
}
double[] marks =
{
    0.0, double.Epsilon, 1609.0 / 1024, 603.0 / 128, 1005.0 / 128, 10.0,
    Math.PI / 2, Math.PI, 3 * Math.PI / 2, 2 * Math.PI, 5 * Math.PI / 2, 3 * Math.PI,
    1.0, 0.5, 2.0, 4.0, 8.0, 1e-300, 2.2250738585072014e-308,
};
foreach (var m in marks)
{
    double up = m, dn = m;
    corpus.Add(m); corpus.Add(-m);
    for (int k = 0; k < 4; k++)
    {
        up = Math.BitIncrement(up); dn = Math.BitDecrement(dn);
        corpus.Add(up); corpus.Add(-up); corpus.Add(dn); corpus.Add(-dn);
    }
}
corpus.AddRange(new[] { double.NaN, -double.NaN, double.PositiveInfinity,
    double.NegativeInfinity, 1e300, -1e300, FromBits(0x7FF0000000000001UL) });

int totalBug = 0;
foreach (var (mode, fn) in new (string, Func<double, double>)[] { ("B64_SIN", B64Sin.Sin), ("B64_COS", B64Sin.Cos) })
{
    var psi = new ProcessStartInfo(oracle)
    {
        RedirectStandardInput = true, RedirectStandardOutput = true, UseShellExecute = false,
    };
    using var proc = Process.Start(psi) ?? throw new InvalidOperationException("cannot start " + oracle);
    var outputTask = proc.StandardOutput.ReadToEndAsync();
    proc.StandardInput.WriteLine(mode);
    foreach (var x in corpus) proc.StandardInput.WriteLine(Bits(x).ToString("x16"));
    proc.StandardInput.Close();
    var lines = outputTask.Result.Split('\n', StringSplitOptions.RemoveEmptyEntries);
    proc.WaitForExit();
    if (lines.Length != corpus.Count)
    {
        Console.WriteLine($"SUMMARY {mode} ok=0 warn=0 bug=1 (oracle returned {lines.Length} lines for {corpus.Count} inputs)");
        totalBug++;
        continue;
    }
    int ok = 0, bug = 0, declined = 0;
    for (int i = 0; i < corpus.Count; i++)
    {
        double x = corpus[i];
        string mine = B64Sin.Accept(x) ? Bits(fn(x)).ToString("x16") : "DECLINE";
        string theirs = lines[i].Trim();
        if (mine == theirs) { ok++; if (mine == "DECLINE") declined++; }
        else
        {
            bug++;
            if (bug <= 10)
                Console.WriteLine($"!! {mode} x={Bits(x):x16} ({x:R}) csharp={mine} oracle={theirs}");
        }
    }
    Console.WriteLine($"# {mode} inputs {corpus.Count}, of which declined {declined}");
    Console.WriteLine($"SUMMARY {mode} ok={ok} warn=0 bug={bug}");
    totalBug += bug;
}

// B64_ARC_PT: (cx, cy, r, t) quadruples; magnitudes from 2^-60 to 2^60 and
// the 2^998 intake cap +-1 ulp, t drawn from the accepted corpus above.
double Mag(Random g)
{
    double m = Math.ScaleB(1.0 + g.NextDouble(), g.Next(-60, 61));
    return g.Next(2) == 0 ? m : -m;
}
var quads = new List<(double cx, double cy, double r, double t)>();
var acc = corpus.Where(B64Sin.Accept).ToArray();
for (int i = 0; i < 200_000; i++)
    quads.Add((Mag(rng), Mag(rng), Mag(rng), acc[rng.Next(acc.Length)]));
double cap = Math.ScaleB(1.0, 998);
foreach (var c in new[] { cap, Math.BitDecrement(cap), Math.BitIncrement(cap), -cap, -Math.BitIncrement(cap),
                          0.0, -0.0, double.Epsilon, double.NaN, double.PositiveInfinity })
{
    quads.Add((c, 1.0, 1.0, 1.0)); quads.Add((1.0, c, 1.0, 2.0)); quads.Add((1.0, 1.0, c, 3.0));
    quads.Add((c, c, c, 5.0)); quads.Add((c, -c, cap, -7.0));
}
{
    const string mode = "B64_ARC_PT";
    var psi = new ProcessStartInfo(oracle)
    {
        RedirectStandardInput = true, RedirectStandardOutput = true, UseShellExecute = false,
    };
    using var proc = Process.Start(psi) ?? throw new InvalidOperationException("cannot start " + oracle);
    var outputTask = proc.StandardOutput.ReadToEndAsync();
    proc.StandardInput.WriteLine(mode);
    foreach (var q in quads)
        proc.StandardInput.WriteLine($"{Bits(q.cx):x16} {Bits(q.cy):x16} {Bits(q.r):x16} {Bits(q.t):x16}");
    proc.StandardInput.Close();
    var lines = outputTask.Result.Split('\n', StringSplitOptions.RemoveEmptyEntries);
    proc.WaitForExit();
    int ok = 0, bug = 0, declined = 0;
    if (lines.Length != quads.Count) bug = 1;
    else
        for (int i = 0; i < quads.Count; i++)
        {
            var (cx, cy, r, t) = quads[i];
            string mine = B64Sin.ArcAccept(cx, cy, r, t)
                ? $"{Bits(B64Sin.ArcX(cx, r, t)):x16} {Bits(B64Sin.ArcY(cy, r, t)):x16}" : "DECLINE";
            string theirs = lines[i].Trim();
            if (mine == theirs) { ok++; if (mine == "DECLINE") declined++; }
            else if (++bug <= 10)
                Console.WriteLine($"!! {mode} in={Bits(cx):x16} {Bits(cy):x16} {Bits(r):x16} {Bits(t):x16} csharp={mine} oracle={theirs}");
        }
    Console.WriteLine($"# {mode} inputs {quads.Count}, of which declined {declined}");
    Console.WriteLine($"SUMMARY {mode} ok={ok} warn=0 bug={bug}");
    totalBug += bug;
}
return totalBug == 0 ? 0 : 1;
