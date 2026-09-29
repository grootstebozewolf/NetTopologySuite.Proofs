// SQL/MM WKT angle differential (#771 / #660).
// Chart θ₀/Δθ (CircleChart + atan) against Math.Atan2, and SQLMM_WKT
// structural identity from the oracle. claimId: none (tools).
// This file was drafted with AI assistance; human review remains required.

using System.Diagnostics;
using System.Globalization;

var root = FindRepoRoot();
int fails = 0;
fails += CheckFixture("ccw", new(0, 0), new(2, 0), new(3, 1), expectPos: true);
fails += CheckFixture("cw", new(0, 0), new(-1, 1), new(3, 1), expectPos: false);
fails += CheckBranchCut("cut", new(0, 1), new(-1, 0), new(0, -1));
fails += CheckCollinear("collinear", new(0, 0), new(1, 0), new(2, 0));
fails += CheckCircle("circle-ccw", new(5, 0), new(0, 5), new(-5, 0), expectCcw: true, expectCut: false);
fails += CheckCircle("circle-cw", new(5, 0), new(0, -5), new(-5, 0), expectCcw: false, expectCut: false);
fails += CheckCircle("circle-cut", new(-1, 0), new(0, -1), new(1, 0), expectCcw: true, expectCut: true);
fails += CheckClosedCs("closed-cs", new(5, 0), new(0, 5));
if (fails != 0)
{
    Console.Error.WriteLine($"SUMMARY bug ({fails} fixture(s))");
    return 1;
}
Console.WriteLine("SUMMARY ok");
return 0;

int CheckFixture(string name, Pt a, Pt m, Pt b, bool expectPos)
{
    var chart = ChartAngles(a, m, b);
    var reference = Atan2Sweep(a, m, b);
    double tol = 1e-9;
    bool th = Math.Abs(Wrap(chart.Theta - reference.Theta)) < tol;
    bool sw = Math.Abs(chart.Sweep - reference.Sweep) < tol;
    bool sign = expectPos ? chart.Sweep > 0 : chart.Sweep < 0;
    bool cross = EndpointCross(chart.O, a, b) > 0;
    string wkt = FormattableString.Invariant(
        $"CIRCULARSTRING ({a.X} {a.Y}, {m.X} {m.Y}, {b.X} {b.Y})");
    string oracle = OracleSqlmm(root, wkt);
    bool parsed = oracle == "OK CIRCULARSTRING XY POINTS 3";
    if (th && sw && sign && cross && parsed)
    {
        Console.WriteLine(
            $"OK {name} theta={chart.Theta:R} sweep={chart.Sweep:R} oracle={oracle}");
        return 0;
    }
    Console.Error.WriteLine(
        $"BUG {name} chart=({chart.Theta:R},{chart.Sweep:R}) " +
        $"ref=({reference.Theta:R},{reference.Sweep:R}) " +
        $"sign={sign} cross={cross} oracle={oracle}");
    return 1;
}

// #770 F2: θ₀ = π/2, Δθ = π. The arc runs through θ = π. Endpoints are
// antipodal, so the radius cross is 0; orientation is the sweep.
int CheckBranchCut(string name, Pt a, Pt m, Pt b)
{
    var chart = ChartAngles(a, m, b);
    var reference = Atan2Sweep(a, m, b);
    double tol = 1e-9;
    bool th = Math.Abs(Wrap(chart.Theta - reference.Theta)) < tol;
    bool sw = Math.Abs(chart.Sweep - reference.Sweep) < tol;
    bool start = Math.Abs(chart.Theta - Math.PI / 2) < tol;
    bool span = Math.Abs(chart.Sweep - Math.PI) < tol;
    bool straddle = chart.Theta < Math.PI && chart.Theta + chart.Sweep > Math.PI;
    bool antipode = Math.Abs(EndpointCross(chart.O, a, b)) < tol;
    string wkt = FormattableString.Invariant(
        $"CIRCULARSTRING ({a.X} {a.Y}, {m.X} {m.Y}, {b.X} {b.Y})");
    string oracle = OracleSqlmm(root, wkt);
    bool parsed = oracle == "OK CIRCULARSTRING XY POINTS 3";
    if (th && sw && start && span && straddle && antipode && parsed)
    {
        Console.WriteLine(
            $"OK {name} theta={chart.Theta:R} sweep={chart.Sweep:R} straddle oracle={oracle}");
        return 0;
    }
    Console.Error.WriteLine(
        $"BUG {name} chart=({chart.Theta:R},{chart.Sweep:R}) " +
        $"ref=({reference.Theta:R},{reference.Sweep:R}) " +
        $"straddle={straddle} antipode={antipode} oracle={oracle}");
    return 1;
}

// Proof fixture col_a, col_b, col_c. try_triple returns AF_Collinear.
// SQLMM_WKT is structural type identity: the text is still a
// CIRCULARSTRING, so the oracle accepts it. The angle chart declines.
int CheckCollinear(string name, Pt a, Pt m, Pt b)
{
    double denom = CircDenom(a, m, b);
    bool declined = denom == 0;
    string wkt = FormattableString.Invariant(
        $"CIRCULARSTRING ({a.X} {a.Y}, {m.X} {m.Y}, {b.X} {b.Y})");
    string oracle = OracleSqlmm(root, wkt);
    bool parsed = oracle == "OK CIRCULARSTRING XY POINTS 3";
    if (declined && parsed)
    {
        Console.WriteLine(
            $"DECLINE {name} denom=0 proof=AF_Collinear oracle={oracle}");
        return 0;
    }
    Console.Error.WriteLine(
        $"BUG {name} denom={denom:R} oracle={oracle}");
    return 1;
}

// ISO CIRCLE(A,B,C): θ₀ = atan2(A−O), sweep = sign(orient)·2π,
// γ(t) = O + r·(cos(θ₀+t·sweep), sin(θ₀+t·sweep)). γ(0)=γ(1)=A.
// CIRCULARSTRING(A,B,A) is a named Decline, not this circle.
int CheckCircle(string name, Pt a, Pt b, Pt c, bool expectCcw, bool expectCut)
{
    double tol = 1e-9;
    double d = CircDenom(a, b, c);
    double na = a.X * a.X + a.Y * a.Y;
    double nb = b.X * b.X + b.Y * b.Y;
    double nc = c.X * c.X + c.Y * c.Y;
    var o = new Pt(
        (na * (b.Y - c.Y) + nb * (c.Y - a.Y) + nc * (a.Y - b.Y)) / d,
        (na * (c.X - b.X) + nb * (a.X - c.X) + nc * (b.X - a.X)) / d);
    double r = Math.Sqrt((a.X - o.X) * (a.X - o.X) + (a.Y - o.Y) * (a.Y - o.Y));
    double theta0 = Math.Atan2(a.Y - o.Y, a.X - o.X);
    double orient = (b.X - a.X) * (c.Y - a.Y) - (b.Y - a.Y) * (c.X - a.X);
    double sweep = Math.CopySign(2 * Math.PI, orient);
    Pt Gamma(double t) => new(
        o.X + r * Math.Cos(theta0 + t * sweep),
        o.Y + r * Math.Sin(theta0 + t * sweep));
    double Param(Pt p)
    {
        double delta = Math.Atan2(p.Y - o.Y, p.X - o.X) - theta0;
        if (sweep > 0)
        {
            if (delta <= 0) delta += 2 * Math.PI;
        }
        else if (delta >= 0)
        {
            delta -= 2 * Math.PI;
        }
        return delta / sweep;
    }
    double tb = Param(b);
    double tc = Param(c);
    bool ends = Near(Gamma(0), a, tol) && Near(Gamma(1), a, tol);
    bool sign = expectCcw ? sweep > 0 && orient > 0 : sweep < 0 && orient < 0;
    bool cut = !expectCut || Math.Abs(theta0 - Math.PI) < tol;
    bool order = 0 < tb && tb < tc && tc < 1;
    bool on = Math.Abs(Dist(o, b) - r) < tol && Math.Abs(Dist(o, c) - r) < tol
        && Near(Gamma(tb), b, tol) && Near(Gamma(tc), c, tol);
    string wkt = FormattableString.Invariant(
        $"CIRCLE ({a.X} {a.Y}, {b.X} {b.Y}, {c.X} {c.Y})");
    string oracle = OracleSqlmm(root, wkt);
    bool parsed = oracle == "OK CIRCLE XY POINTS 3";
    if (ends && sign && cut && order && on && parsed)
    {
        Console.WriteLine(
            $"OK {name} theta0={theta0:R} sweep={sweep:R} tB={tb:R} tC={tc:R} oracle={oracle}");
        return 0;
    }
    Console.Error.WriteLine(
        $"BUG {name} theta0={theta0:R} sweep={sweep:R} orient={orient:R} " +
        $"tB={tb:R} tC={tc:R} ends={ends} sign={sign} cut={cut} order={order} on={on} oracle={oracle}");
    return 1;
}

int CheckClosedCs(string name, Pt a, Pt b)
{
    string wkt = FormattableString.Invariant(
        $"CIRCULARSTRING ({a.X} {a.Y}, {b.X} {b.Y}, {a.X} {a.Y})");
    string oracle = OracleSqlmm(root, wkt);
    bool parsed = oracle == "OK CIRCULARSTRING XY POINTS 3";
    if (parsed)
    {
        Console.WriteLine(
            $"DECLINE {name} proof=ID_CsClosedDegenerate oracle={oracle}");
        return 0;
    }
    Console.Error.WriteLine($"BUG {name} oracle={oracle}");
    return 1;
}

static bool Near(Pt p, Pt q, double tol) =>
    Math.Abs(p.X - q.X) < tol && Math.Abs(p.Y - q.Y) < tol;

static double Dist(Pt p, Pt q) =>
    Math.Sqrt((p.X - q.X) * (p.X - q.X) + (p.Y - q.Y) * (p.Y - q.Y));

static double CircDenom(Pt a, Pt mid, Pt b) =>
    2 * (a.X * (mid.Y - b.Y) + mid.X * (b.Y - a.Y) + b.X * (a.Y - mid.Y));

static Angles ChartAngles(Pt a, Pt mid, Pt b)
{
    double d = 2 * (a.X * (mid.Y - b.Y) + mid.X * (b.Y - a.Y) + b.X * (a.Y - mid.Y));
    double na = a.X * a.X + a.Y * a.Y;
    double nb = mid.X * mid.X + mid.Y * mid.Y;
    double nc = b.X * b.X + b.Y * b.Y;
    var o = new Pt(
        (na * (mid.Y - b.Y) + nb * (b.Y - a.Y) + nc * (a.Y - mid.Y)) / d,
        (na * (b.X - mid.X) + nb * (a.X - b.X) + nc * (mid.X - a.X)) / d);
    var n = new Pt((a.X + b.X) / 2, (a.Y + b.Y) / 2);
    double mx = mid.X - o.X, my = mid.Y - o.Y;
    double wx = n.X - mid.X, wy = n.Y - mid.Y;
    double k = -2 * (mx * wx + my * wy) / (wx * wx + wy * wy);
    var q = new Pt(mid.X + k * wx, mid.Y + k * wy);
    double ux = o.X - q.X, uy = o.Y - q.Y;
    double za = Zeta(ux, uy, a.X - o.X, a.Y - o.Y);
    double zb = Zeta(ux, uy, b.X - o.X, b.Y - o.Y);
    double raw = Math.Atan2(uy, ux) + 2 * Math.Atan(za);
    return new Angles(o, Principal(raw), 2 * (Math.Atan(zb) - Math.Atan(za)));
}

static Angles Atan2Sweep(Pt a, Pt mid, Pt b)
{
    double d = 2 * (a.X * (mid.Y - b.Y) + mid.X * (b.Y - a.Y) + b.X * (a.Y - mid.Y));
    double na = a.X * a.X + a.Y * a.Y;
    double nb = mid.X * mid.X + mid.Y * mid.Y;
    double nc = b.X * b.X + b.Y * b.Y;
    var o = new Pt(
        (na * (mid.Y - b.Y) + nb * (b.Y - a.Y) + nc * (a.Y - mid.Y)) / d,
        (na * (b.X - mid.X) + nb * (a.X - b.X) + nc * (mid.X - a.X)) / d);
    double thA = Math.Atan2(a.Y - o.Y, a.X - o.X);
    double thB = Math.Atan2(b.Y - o.Y, b.X - o.X);
    double thM = Math.Atan2(mid.Y - o.Y, mid.X - o.X);
    double ccw = thB - thA;
    if (ccw <= 0) ccw += 2 * Math.PI;
    double along = thM - thA;
    if (along < 0) along += 2 * Math.PI;
    if (along >= 2 * Math.PI) along -= 2 * Math.PI;
    double sweep = along <= ccw ? ccw : ccw - 2 * Math.PI;
    return new Angles(o, thA, sweep);
}

static double Zeta(double ux, double uy, double vx, double vy) =>
    (ux * vy - uy * vx) / (ux * ux + uy * uy + ux * vx + uy * vy);

static double Principal(double a)
{
    if (a <= -Math.PI) return a + 2 * Math.PI;
    if (Math.PI < a) return a - 2 * Math.PI;
    return a;
}

static double Wrap(double a)
{
    while (a <= -Math.PI) a += 2 * Math.PI;
    while (a > Math.PI) a -= 2 * Math.PI;
    return a;
}

static double EndpointCross(Pt o, Pt a, Pt b) =>
    (a.X - o.X) * (b.Y - o.Y) - (a.Y - o.Y) * (b.X - o.X);

static string OracleSqlmm(string root, string wkt)
{
    string? env = Environment.GetEnvironmentVariable("ORACLE");
    string bin = env is { Length: > 0 } && File.Exists(env)
        ? env
        : FirstExisting(
            Path.Combine(root, "oracle", "oracle_bin"),
            Path.Combine(root, "oracle", "sqlmm_wkt_bin"));
    var psi = new ProcessStartInfo
    {
        FileName = bin,
        RedirectStandardInput = true,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        UseShellExecute = false,
    };
    using var p = Process.Start(psi) ?? throw new InvalidOperationException("oracle start");
    p.StandardInput.Write("SQLMM_WKT\n");
    p.StandardInput.Write(wkt);
    p.StandardInput.Write('\n');
    p.StandardInput.Close();
    string stdout = p.StandardOutput.ReadToEnd().Trim();
    if (!p.WaitForExit(20000))
        throw new TimeoutException("oracle timeout");
    return stdout.Split('\n', StringSplitOptions.RemoveEmptyEntries).FirstOrDefault() ?? "";
}

static string FirstExisting(params string[] paths)
{
    foreach (var p in paths)
        if (File.Exists(p)) return p;
    throw new FileNotFoundException(
        "SQLMM_WKT oracle not found (set ORACLE, or build oracle/sqlmm_wkt_bin)");
}

static string FindRepoRoot()
{
    var dir = new DirectoryInfo(AppContext.BaseDirectory);
    while (dir is not null)
    {
        if (File.Exists(Path.Combine(dir.FullName, "build.cake")))
            return dir.FullName;
        dir = dir.Parent;
    }
    return Directory.GetCurrentDirectory();
}

readonly record struct Pt(double X, double Y);
readonly record struct Angles(Pt O, double Theta, double Sweep);
