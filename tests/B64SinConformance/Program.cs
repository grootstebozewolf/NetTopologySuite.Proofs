// S3-S9 conformance harness: C# B64Sin.Sin / Cos / ArcX / ArcY / FresnelC /
// FresnelS / ClothoidIcos / ClothoidIsin / SegGOutcome vs the Rocq-extracted
// oracle (modes B64_SIN, B64_COS, B64_ARC_PT, B64_FRESNEL, B64_CLOTHOID,
// B64_SEG_G), compared on output BITS and decisions.  Corpus: seeded uniform inputs on [-10, 10],
// random bit patterns in the accepted range (all binades, subnormals),
// thresholds / caps / multiples of pi +-4 ulp, signed zeros, and rejected
// inputs (NaN, infinities, just outside the cap) for DECLINE parity.
// Usage: dotnet run --project tests/B64SinConformance [-- ORACLE_BIN]
//        (default: $ORACLE or oracle/oracle_bin).  Exit 0 = bit-identical.
//   GOLDEN_OUT=dir   also write the oracle's answers to dir/<MODE>.out with the
//                    corpus hash dir/<MODE>.in.sha256 (CI x64 job);
//   GOLDEN_IN=dir    compare against those files instead of running the oracle
//                    (CI arm64 job: the x86-64 oracle_bin cannot run there).
//                    The corpus is seeded, so both sides see identical inputs;
//                    the hash check fails loudly if they do not.
// AI assistance disclosure: AI-drafted; human review pending.
using System.Diagnostics;
using System.Security.Cryptography;
using System.Text;
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


var goldenIn = Environment.GetEnvironmentVariable("GOLDEN_IN");
var goldenOut = Environment.GetEnvironmentVariable("GOLDEN_OUT");
if (!string.IsNullOrEmpty(goldenOut)) Directory.CreateDirectory(goldenOut);

// One oracle query: the mode header, then one input line per case.
string[] Query(string mode, IEnumerable<string> inputs)
{
    var inLines = inputs.ToList();
    string hash = Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(string.Join("\n", inLines))));
    if (!string.IsNullOrEmpty(goldenIn))
    {
        string want = File.ReadAllText(Path.Combine(goldenIn, mode + ".in.sha256")).Trim();
        if (want != hash)
            throw new InvalidOperationException($"{mode}: corpus hash {hash} differs from golden {want}");
        return File.ReadAllText(Path.Combine(goldenIn, mode + ".out"))
                   .Split('\n', StringSplitOptions.RemoveEmptyEntries);
    }
    var psi = new ProcessStartInfo(oracle)
    {
        RedirectStandardInput = true, RedirectStandardOutput = true, UseShellExecute = false,
    };
    using var proc = Process.Start(psi) ?? throw new InvalidOperationException("cannot start " + oracle);
    var outputTask = proc.StandardOutput.ReadToEndAsync();
    proc.StandardInput.WriteLine(mode);
    foreach (var l in inLines) proc.StandardInput.WriteLine(l);
    proc.StandardInput.Close();
    string text = outputTask.Result;
    proc.WaitForExit();
    if (!string.IsNullOrEmpty(goldenOut))
    {
        File.WriteAllText(Path.Combine(goldenOut, mode + ".out"), text);
        File.WriteAllText(Path.Combine(goldenOut, mode + ".in.sha256"), hash + "\n");
    }
    return text.Split('\n', StringSplitOptions.RemoveEmptyEntries);
}

int totalBug = 0;
foreach (var (mode, fn) in new (string, Func<double, double>)[] { ("B64_SIN", B64Sin.Sin), ("B64_COS", B64Sin.Cos) })
{
    var lines = Query(mode, corpus.Select(x => Bits(x).ToString("x16")));
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
    var lines = Query(mode, quads.Select(q => $"{Bits(q.cx):x16} {Bits(q.cy):x16} {Bits(q.r):x16} {Bits(q.t):x16}"));
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

// B64_FRESNEL: uniform on [-5/2, 5/2], random accepted bit patterns, the cap
// +-4 ulp, signed zeros, subnormals, NaN / inf.
var fx = new List<double>();
for (int i = 0; i < 200_000; i++) fx.Add(rng.NextDouble() * 5.0 - 2.5);
for (int kept2 = 0; kept2 < 50_000;)
{
    rng.NextBytes(buf);
    double v = FromBits(BitConverter.ToUInt64(buf, 0));
    if (double.IsFinite(v) && Math.Abs(v) <= 2.5) { fx.Add(v); kept2++; }
}
foreach (var m in new[] { 2.5, 2.298, 1.0, 0.0, double.Epsilon, 2.2250738585072014e-308 })
{
    double up = m, dn = m;
    fx.Add(m); fx.Add(-m);
    for (int k = 0; k < 4; k++)
    {
        up = Math.BitIncrement(up); dn = Math.BitDecrement(dn);
        fx.Add(up); fx.Add(-up); fx.Add(dn); fx.Add(-dn);
    }
}
fx.AddRange(new[] { double.NaN, double.PositiveInfinity, double.NegativeInfinity, 3.0, -1e300 });
{
    const string mode = "B64_FRESNEL";
    var lines = Query(mode, fx.Select(x => Bits(x).ToString("x16")));
    int ok = 0, bug = 0, declined = 0;
    if (lines.Length != fx.Count) bug = 1;
    else
        for (int i = 0; i < fx.Count; i++)
        {
            double x = fx[i];
            string mine = B64Sin.FresnelAccept(x)
                ? $"{Bits(B64Sin.FresnelC(x)):x16} {Bits(B64Sin.FresnelS(x)):x16}" : "DECLINE_FRESNEL_RANGE";
            string theirs = lines[i].Trim();
            if (mine == theirs) { ok++; if (mine.StartsWith("DECLINE")) declined++; }
            else if (++bug <= 10)
                Console.WriteLine($"!! {mode} x={Bits(x):x16} ({x:R}) csharp={mine} oracle={theirs}");
        }
    Console.WriteLine($"# {mode} inputs {fx.Count}, of which declined {declined}");
    Console.WriteLine($"SUMMARY {mode} ok={ok} warn=0 bug={bug}");
    totalBug += bug;
}

// B64_CLOTHOID: (A, s, sigma); A over 2^-40..2^40, s = x sqrt2 A with x near
// the 5/2 cap, the A / s caps +-1 ulp, zeros, NaN / inf.
var cq = new List<(double a, double s, bool neg)>();
for (int i = 0; i < 150_000; i++)
{
    double a = Math.ScaleB(1.0 + rng.NextDouble(), rng.Next(-40, 41));
    double x = rng.NextDouble() * 5.2 - 2.6;
    cq.Add((a, x * Math.Sqrt(2.0) * a, rng.Next(2) == 1));
}
double c500 = Math.ScaleB(1.0, 500), cm500 = Math.ScaleB(1.0, -500);
foreach (var a in new[] { cm500, Math.BitDecrement(cm500), Math.BitIncrement(cm500), c500, Math.BitIncrement(c500),
                          1.0, 100.0, 0.0, -1.0, double.NaN, double.PositiveInfinity })
    foreach (var s in new[] { 0.0, -0.0, 1.0, 3.25, -3.25, 3.5355339059327373, c500, Math.BitIncrement(c500),
                              double.Epsilon, double.NaN, double.NegativeInfinity })
    {
        cq.Add((a, s, false)); cq.Add((a, s, true));
    }
{
    const string mode = "B64_CLOTHOID";
    var lines = Query(mode, cq.Select(q => $"{Bits(q.a):x16} {Bits(q.s):x16} {(q.neg ? 1 : 0)}"));
    int ok = 0, bug = 0, declined = 0;
    if (lines.Length != cq.Count) bug = 1;
    else
        for (int i = 0; i < cq.Count; i++)
        {
            var (a, s, neg) = cq[i];
            string mine = B64Sin.ClothoidAccept(a, s)
                ? $"{Bits(B64Sin.ClothoidIcos(a, s)):x16} {Bits(B64Sin.ClothoidIsin(neg, a, s)):x16}"
                : "DECLINE_FRESNEL_RANGE";
            string theirs = lines[i].Trim();
            if (mine == theirs) { ok++; if (mine.StartsWith("DECLINE")) declined++; }
            else if (++bug <= 10)
                Console.WriteLine($"!! {mode} in={Bits(a):x16} {Bits(s):x16} {neg} csharp={mine} oracle={theirs}");
        }
    Console.WriteLine($"# {mode} inputs {cq.Count}, of which declined {declined}");
    Console.WriteLine($"SUMMARY {mode} ok={ok} warn=0 bug={bug}");
    totalBug += bug;
}

// B64_SEG_G: the margin boundary of g = t - sin t against 2^-48 lies near
// |t| = 2.6e-5 .. 2.9e-5; sweep it ulp by ulp, plus the accepted corpus.
var gx = new List<double>(corpus);
for (double t0 = 2.0e-5; t0 < 3.5e-5; t0 += 1e-9) { gx.Add(t0); gx.Add(-t0); }
foreach (var m in new[] { 2.7e-5, 2.8e-5, 2.9e-5 })
{
    double up = m, dn = m;
    for (int k = 0; k < 2000; k++) { up = Math.BitIncrement(up); dn = Math.BitDecrement(dn); gx.Add(up); gx.Add(dn); gx.Add(-up); }
}
{
    const string mode = "B64_SEG_G";
    var lines = Query(mode, gx.Select(t => Bits(t).ToString("x16")));
    int ok = 0, bug = 0, pos = 0, neg = 0, dec = 0;
    if (lines.Length != gx.Count) bug = 1;
    else
        for (int i = 0; i < gx.Count; i++)
        {
            string mine = B64Sin.SegGOutcome(gx[i]);
            string theirs = lines[i].Trim();
            if (mine == theirs)
            {
                ok++;
                if (mine.StartsWith("POSITIVE")) pos++; else if (mine.StartsWith("NEGATIVE")) neg++; else dec++;
            }
            else if (++bug <= 10)
                Console.WriteLine($"!! {mode} t={Bits(gx[i]):x16} ({gx[i]:R}) csharp={mine} oracle={theirs}");
        }
    Console.WriteLine($"# {mode} inputs {gx.Count}: POSITIVE {pos}, NEGATIVE {neg}, DECLINE {dec}");
    Console.WriteLine($"SUMMARY {mode} ok={ok} warn=0 bug={bug}");
    totalBug += bug;
}
return totalBug == 0 ? 0 : 1;
