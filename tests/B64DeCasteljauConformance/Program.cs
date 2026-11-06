// Proof-to-code conformance harness for the proved binary64 de Casteljau
// evaluator.  Replays DIR/B64_DECASTELJAU.in (one query per line:
// "t c0 c1 ... cn", 16-hex-digit bit patterns) through the C# port and
// compares the answer string with DIR/B64_DECASTELJAU.out, the answers of
// the Rocq-extracted oracle (oracle_bin B64_DECASTELJAU), bit for bit.
// Also reports platform/runtime and how FMA-sensitive the corpus is.
// Usage: dotnet run --project tests/B64DeCasteljauConformance -c Release -- DIR
//        Exit 0 = zero mismatches (and the FMA canary condition holds).
// AI assistance disclosure: AI-drafted; human review pending.
using System.Globalization;
using System.Runtime.InteropServices;
using NTS.Proofs.Numerics;

static string H(double v) => unchecked((ulong)BitConverter.DoubleToInt64Bits(v)).ToString("x16");
static double D(string h) => BitConverter.Int64BitsToDouble(unchecked((long)ulong.Parse(h, NumberStyles.HexNumber)));

// Test-only references: the same triangular scheme with a CONTRACTED node.
// They are NOT the proved program; they exist to measure how many corpus
// results would change if a JIT fused the node, i.e. the corpus's power to
// detect contraction.
static double Fused(double[] cs, double t, int variant)
{
    double s = 1.0 - t;
    var row = (double[])cs.Clone();
    for (int round = 1; round < row.Length; round++)
        for (int i = 0; i + round < row.Length; i++)
            row[i] = variant == 1
                ? Math.FusedMultiplyAdd(s, row[i], t * row[i + 1])   // fl(s x + fl(t y))
                : Math.FusedMultiplyAdd(t, row[i + 1], s * row[i]);  // fl(t y + fl(s x))
    return row[0];
}

if (args.Length < 1)
{
    Console.Error.WriteLine("usage: dotnet run --project tests/B64DeCasteljauConformance -c Release -- CORPUS_DIR");
    return 2;
}
string dir = args[0];
Console.WriteLine($"# runtime {RuntimeInformation.FrameworkDescription} on {RuntimeInformation.OSDescription} " +
                  $"{RuntimeInformation.ProcessArchitecture}; Fma.IsSupported=" +
                  $"{System.Runtime.Intrinsics.X86.Fma.IsSupported}; Math.FusedMultiplyAdd is explicit-only");

var ins = File.ReadAllLines(Path.Combine(dir, "B64_DECASTELJAU.in")).Where(l => l.Length > 0).ToArray();
var outs = File.ReadAllLines(Path.Combine(dir, "B64_DECASTELJAU.out")).Where(l => l.Length > 0).ToArray();
if (ins.Length != outs.Length)
{
    Console.WriteLine($"!! {ins.Length} inputs but {outs.Length} oracle answers");
    Console.WriteLine("SUMMARY B64_DECASTELJAU ok=0 warn=0 bug=1");
    return 1;
}

int ok = 0, bug = 0, certified = 0;
var declines = new SortedDictionary<string, int>();
int sens1 = 0, sens2 = 0, sensEither = 0, multiNode = 0;
for (int i = 0; i < ins.Length; i++)
{
    var f = ins[i].Split(' ', StringSplitOptions.RemoveEmptyEntries);
    double t = D(f[0]);
    var cs = new double[f.Length - 1];
    for (int k = 1; k < f.Length; k++) cs[k - 1] = D(f[k]);
    string r = B64DeCasteljau.Eval(cs, t, out double v);
    string mine = r == "CERTIFIED" ? "CERTIFIED " + H(v) : r;
    string theirs = outs[i].Trim();
    if (mine == theirs)
    {
        ok++;
        if (r == "CERTIFIED")
        {
            certified++;
            if (cs.Length > 1)
            {
                multiNode++;
                bool d1 = H(Fused(cs, t, 1)) != H(v), d2 = H(Fused(cs, t, 2)) != H(v);
                if (d1) sens1++;
                if (d2) sens2++;
                if (d1 || d2) sensEither++;
            }
        }
        else declines[r] = declines.GetValueOrDefault(r) + 1;
    }
    else if (++bug <= 10)
        Console.WriteLine($"!! in=[{ins[i]}] csharp={mine} oracle={theirs}");
}
Console.WriteLine($"# B64_DECASTELJAU cases {ins.Length}: certified {certified}, declined {ins.Length - certified}");
foreach (var (k, n) in declines) Console.WriteLine($"#   {k} {n}");
Console.WriteLine($"# FMA canary: of {multiNode} certified multi-node cases, results that would change under " +
                  $"fused node variants: fl(s*x + fl(t*y)) {sens1}, fl(t*y + fl(s*x)) {sens2}, either {sensEither}");
// The corpus must be able to see contraction: require a substantial share of
// FMA-sensitive cases, otherwise bit identity would not exclude FMA.
bool canary = multiNode > 0 && sensEither * 10 >= multiNode;   // >= 10 %
if (!canary) { Console.WriteLine("!! FMA canary too weak: corpus cannot detect contraction"); bug++; }
Console.WriteLine($"SUMMARY B64_DECASTELJAU ok={ok} warn=0 bug={bug}");
return bug == 0 ? 0 : 1;
