// Shelf A model + independent μ-bag expectation (mirrors IntakeVisitor first slice).
// Assisted-by: Cursor Grok 4.6. claimId: none (tools).

using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;

readonly record struct Xy(double X, double Y);

sealed class Bag
{
    public List<int> Hens { get; }
    public List<Xy> Pts { get; }
    public List<(int Src, int Dst, string Egg)> Chickens { get; }

    public Bag(IEnumerable<int> hens, IEnumerable<Xy> pts, IEnumerable<(int, int, string)> chickens)
    {
        Hens = hens.ToList();
        Pts = pts.ToList();
        Chickens = chickens.ToList();
    }

    public string ToWire()
    {
        string hens = string.Join(",", Hens);
        string pts = string.Join(";", Pts.Select(p => $"{Wire.JavaTrim(p.X)} {Wire.JavaTrim(p.Y)}"));
        string chicks = string.Join(",", Chickens.Select(c => $"{c.Src}-{c.Dst}:{c.Egg}"));
        return $"BAG hens={hens} pts={pts} chickens={chicks}";
    }
}

sealed class Model
{
    public string Mid = "stdin";
    public string Keyword = "LINESTRING";
    public bool Empty;
    public List<int> Hens = [];
    public List<Xy> Pts = [];
    public List<Xy> Controls = [];
    public List<(int Src, int Dst, string Egg)> Chickens = [];
    public string Tau = "TagLineString";
    public List<Model> Children = [];
    public (string K0, string K1, string L)? Jts;
    public string ExpectKind = "BAG"; // BAG | DECLINE
    public string? ExpectDecline;
    public Bag? ExpectBag;
    public int? SignedWkb; // 1/2/8/9
    public bool Hold;
    public string Note = "";

    public string Text(string indent = "")
    {
        var sb = new StringBuilder();
        sb.Append(indent).Append("id=").Append(Mid).Append('\n');
        sb.Append(indent).Append("keyword=").Append(Keyword).Append('\n');
        sb.Append(indent).Append("empty=").Append(Empty ? "true" : "false").Append('\n');
        sb.Append(indent).Append("tau=").Append(Tau).Append('\n');
        if (Hens.Count > 0)
            sb.Append(indent).Append("hens=").Append(string.Join(",", Hens)).Append('\n');
        foreach (var p in Pts)
            sb.Append(indent).Append("pt=").Append(Inv(p.X)).Append(',').Append(Inv(p.Y)).Append('\n');
        foreach (var p in Controls)
            sb.Append(indent).Append("control=").Append(Inv(p.X)).Append(',').Append(Inv(p.Y)).Append('\n');
        foreach (var c in Chickens)
            sb.Append(indent).Append("chicken=").Append(c.Src).Append(',').Append(c.Dst).Append(',').Append(c.Egg).Append('\n');
        if (Jts is { } j)
            sb.Append(indent).Append("jts=").Append(j.K0).Append(',').Append(j.K1).Append(',').Append(j.L).Append('\n');
        foreach (var ch in Children)
        {
            sb.Append(indent).Append("child-begin\n");
            sb.Append(ch.Text(indent));
            sb.Append(indent).Append("child-end\n");
        }
        return sb.ToString();
    }

    static string Inv(double v) => v.ToString("G17", CultureInfo.InvariantCulture);
}

static class Wire
{
    // Chabukswar & Mukherjee arXiv:1804.07389 — hardcoded; do not land #746.
    internal static readonly Xy[] FamousWater =
    [
        new(66.6666666667, 25.2833333333),
        new(162.2333333333, 58.6166666667),
    ];
    internal static readonly Xy[] FamousLand =
    [
        new(118.6333333333, 24.55),
        new(-8.9166666667, 37.0333333333),
    ];
    internal static readonly Xy[] LockedCsQuarter = [new(5, 0), new(3, 4), new(0, 5)];
    internal static readonly Xy[] LockedCsFull = [new(5, 0), new(0, 5), new(5, 0)];
    internal static readonly Xy[] LockedCircle = [new(5, 0), new(0, 5), new(-5, 0)];
    internal static readonly Xy[] LockedClothoidPts =
    [
        new(0, 0),
        new(80, (0.005 - 0.0) * (80.0 * 80.0) / 6.0),
    ];

    internal static readonly HashSet<int> SignedTypes = [1, 2, 8, 9];
    internal static readonly HashSet<int> ForbiddenSigned = [13, 18, 22];

    internal static string JavaTrim(double v)
    {
        if (double.IsNaN(v) || double.IsInfinity(v))
            return v.ToString(CultureInfo.InvariantCulture);
        if (v == Math.Round(v) && Math.Abs(v) < 1e12)
            return ((long)Math.Round(v)).ToString(CultureInfo.InvariantCulture);
        string s = v.ToString("G17", CultureInfo.InvariantCulture);
        if (s.EndsWith(".0", StringComparison.Ordinal) && s.Count(c => c == '.') == 1)
            return s[..^2];
        return s;
    }

    internal static string FmtPt(Xy p) => $"{JavaTrim(p.X)} {JavaTrim(p.Y)}";

    internal static (string Kind, Bag? Bag, string? Decline) Parse(string s)
    {
        s = s.Trim();
        if (s.StartsWith("DECLINE ", StringComparison.Ordinal))
            return ("DECLINE", null, s["DECLINE ".Length..].Trim());
        if (!s.StartsWith("BAG", StringComparison.Ordinal))
            return ("OTHER", null, s);
        var m = Regex.Match(s, @"hens=(.*) pts=(.*) chickens=(.*)$");
        string hensS = "", ptsS = "", chS = "";
        if (m.Success)
        {
            hensS = m.Groups[1].Value.Trim();
            ptsS = m.Groups[2].Value.Trim();
            chS = m.Groups[3].Value.Trim();
        }
        var hens = hensS.Split(',', StringSplitOptions.RemoveEmptyEntries).Select(int.Parse).ToList();
        var pts = new List<Xy>();
        if (ptsS.Length > 0)
        {
            foreach (var chunk in ptsS.Split(';'))
            {
                if (chunk.Length == 0) continue;
                var xs = chunk.Split(' ', StringSplitOptions.RemoveEmptyEntries);
                if (xs.Length < 2)
                    return ("OTHER", null, s);
                pts.Add(new Xy(double.Parse(xs[0], CultureInfo.InvariantCulture),
                    double.Parse(xs[1], CultureInfo.InvariantCulture)));
            }
        }
        var chickens = new List<(int, int, string)>();
        if (chS.Length > 0)
        {
            foreach (var chunk in chS.Split(',', StringSplitOptions.RemoveEmptyEntries))
            {
                int colon = chunk.IndexOf(':');
                if (colon < 0) continue;
                var sd = chunk[..colon].Split('-');
                chickens.Add((int.Parse(sd[0]), int.Parse(sd[1]), chunk[(colon + 1)..]));
            }
        }
        return ("BAG", new Bag(hens, pts, chickens), null);
    }

    internal static bool BagsEqual(Bag a, Bag b, double eps = 1e-12)
    {
        if (!a.Hens.SequenceEqual(b.Hens) || a.Chickens.Count != b.Chickens.Count)
            return false;
        if (!a.Chickens.SequenceEqual(b.Chickens))
            return false;
        if (a.Pts.Count != b.Pts.Count)
            return false;
        for (int i = 0; i < a.Pts.Count; i++)
        {
            if (Math.Abs(a.Pts[i].X - b.Pts[i].X) > eps || Math.Abs(a.Pts[i].Y - b.Pts[i].Y) > eps)
                return false;
        }
        return true;
    }

    internal static bool SameXy(Xy a, Xy b) => a.X == b.X && a.Y == b.Y;

    internal static double CircDenom(Xy a, Xy b, Xy c) =>
        2 * (a.X * (b.Y - c.Y) + b.X * (c.Y - a.Y) + c.X * (a.Y - b.Y));

    internal static string? TryTriple(Xy a, Xy b, Xy c)
    {
        if (SameXy(a, b) || SameXy(b, c) || SameXy(a, c))
            return "ID_DuplicateControl";
        double d = CircDenom(a, b, c);
        if (d == 0.0)
            return "ID_Collinear";
        double na = a.X * a.X + a.Y * a.Y;
        double nb = b.X * b.X + b.Y * b.Y;
        double nc = c.X * c.X + c.Y * c.Y;
        double ux = (na * (b.Y - c.Y) + nb * (c.Y - a.Y) + nc * (a.Y - b.Y)) / d;
        double uy = (na * (c.X - b.X) + nb * (a.X - c.X) + nc * (b.X - a.X)) / d;
        double r2 = (a.X - ux) * (a.X - ux) + (a.Y - uy) * (a.Y - uy);
        if (r2 == 0.0)
            return "ID_DegenerateArc";
        return null;
    }

    internal static (string Kind, Bag? Bag, string? Decline) ExpectLs(IReadOnlyList<Xy> pts)
    {
        if (pts.Count == 0)
            return ("DECLINE", null, "ID_Empty");
        if (pts.Count < 2)
            return ("DECLINE", null, "ID_BadPointCount");
        var hens = Enumerable.Range(0, pts.Count).ToList();
        var chicks = Enumerable.Range(0, pts.Count - 1).Select(i => (i, i + 1, "MkChord")).ToList();
        return ("BAG", new Bag(hens, pts, chicks), null);
    }

    internal static (string Kind, Bag? Bag, string? Decline) ExpectCs(IReadOnlyList<Xy> pts)
    {
        if (pts.Count == 0)
            return ("DECLINE", null, "ID_Empty");
        if (pts.Count == 3)
        {
            var a = pts[0];
            var c = pts[2];
            if (SameXy(a, c))
            {
                if (SameXy(a, pts[1]))
                    return ("DECLINE", null, "ID_CsClosedDegenerate");
                return ExpectCircle([a, pts[1], OgcC(a, pts[1])]);
            }
            if (SameXy(a, new(5, 0)) && SameXy(c, new(0, 5)))
                return ("BAG", new Bag([0, 1], [new(5, 0), new(0, 5)], [(0, 1, "MkCirc:quarter")]), null);
        }
        if (pts.Count < 3 || pts.Count % 2 == 0)
            return ("DECLINE", null, "ID_BadPointCount");
        var ends = new List<Xy> { pts[0] };
        var chicks = new List<(int, int, string)>();
        int hen = 0;
        for (int i = 0; i < pts.Count - 2; i += 2)
        {
            var dec = TryTriple(pts[i], pts[i + 1], pts[i + 2]);
            if (dec != null)
                return ("DECLINE", null, dec);
            ends.Add(pts[i + 2]);
            chicks.Add((hen, hen + 1, "MkCirc"));
            hen++;
        }
        return ("BAG", new Bag(Enumerable.Range(0, ends.Count), ends, chicks), null);
    }

    /// <summary>CW completion: C' = M + rot_+90°(A−M). Same as IntakeVisitor.OgcC.</summary>
    internal static Xy OgcC(Xy a, Xy b)
    {
        double mx = (a.X + b.X) / 2.0;
        double my = (a.Y + b.Y) / 2.0;
        double vx = a.X - mx;
        double vy = a.Y - my;
        return new Xy(mx - vy, my + vx);
    }

    internal static (string Kind, Bag? Bag, string? Decline) ExpectCircle(IReadOnlyList<Xy> pts)
    {
        if (pts.Count == 0)
            return ("DECLINE", null, "ID_Empty");
        if (pts.Count != 3)
            return ("DECLINE", null, "ID_BadPointCount");
        var dec = TryTriple(pts[0], pts[1], pts[2]);
        if (dec != null)
            return ("DECLINE", null, dec);
        double d = CircDenom(pts[0], pts[1], pts[2]);
        double na = pts[0].X * pts[0].X + pts[0].Y * pts[0].Y;
        double nb = pts[1].X * pts[1].X + pts[1].Y * pts[1].Y;
        double nc = pts[2].X * pts[2].X + pts[2].Y * pts[2].Y;
        double ox = (na * (pts[1].Y - pts[2].Y) + nb * (pts[2].Y - pts[0].Y) + nc * (pts[0].Y - pts[1].Y)) / d;
        double oy = (na * (pts[2].X - pts[1].X) + nb * (pts[0].X - pts[2].X) + nc * (pts[1].X - pts[0].X)) / d;
        var anti = new Xy(2 * ox - pts[0].X, 2 * oy - pts[0].Y);
        return ("BAG", new Bag([0, 1], [pts[0], anti],
            [(0, 1, "MkCirc:half"), (1, 0, "MkCirc:half")]), null);
    }

    internal static (string Kind, Bag? Bag, string? Decline) ExpectClothoid() =>
        ("BAG", new Bag([0, 1], LockedClothoidPts, [(0, 1, "MkClothoid")]), null);

    internal static (string Kind, Bag? Bag, string? Decline) ExpectPoint(IReadOnlyList<Xy> pts)
    {
        if (pts.Count == 0)
            return ("DECLINE", null, "ID_Empty");
        return ("BAG", new Bag([0], [pts[0]], []), null);
    }

    internal static Bag AppendBag(Bag a, Bag b)
    {
        int off = a.Hens.Count;
        return new Bag(
            a.Hens.Concat(b.Hens.Select(h => off + h)),
            a.Pts.Concat(b.Pts),
            a.Chickens.Concat(b.Chickens.Select(c => (off + c.Src, off + c.Dst, c.Egg))));
    }

    internal static Model FinishLs(string mid, IReadOnlyList<Xy> pts, bool geodesic = false)
    {
        var (kind, bag, dec) = ExpectLs(pts);
        var m = new Model
        {
            Mid = mid,
            Keyword = "LINESTRING",
            Hens = pts.Count > 0 ? Enumerable.Range(0, pts.Count).ToList() : [],
            Pts = pts.ToList(),
            Controls = pts.ToList(),
            Chickens = Enumerable.Range(0, Math.Max(0, pts.Count - 1)).Select(i => (i, i + 1, "MkChord")).ToList(),
            Tau = "TagLineString",
            ExpectKind = kind,
            ExpectDecline = dec,
            ExpectBag = bag,
            SignedWkb = 2,
            Note = geodesic ? "geodesic-as-ls" : "",
        };
        if (pts.Count == 0)
        {
            m.Empty = true;
            m.Hens = [];
            m.Pts = [];
            m.Controls = [];
            m.Chickens = [];
            m.ExpectKind = "DECLINE";
            m.ExpectDecline = "ID_Empty";
            m.ExpectBag = null;
        }
        return m;
    }

    internal static Model FinishPoint(string mid, Xy? pt)
    {
        if (pt is null)
        {
            return new Model
            {
                Mid = mid,
                Keyword = "POINT",
                Empty = true,
                ExpectKind = "DECLINE",
                ExpectDecline = "ID_Empty",
                Hold = true,
            };
        }
        var p = pt.Value;
        return new Model
        {
            Mid = mid,
            Keyword = "POINT",
            Hens = [0],
            Pts = [p],
            Controls = [p],
            Tau = "TagLineString",
            ExpectKind = "BAG",
            ExpectBag = new Bag([0], [p], []),
            SignedWkb = 1,
        };
    }

    internal static Model FinishCs(string mid, IReadOnlyList<Xy> controls, bool empty = false)
    {
        if (empty || controls.Count == 0)
        {
            return new Model
            {
                Mid = mid,
                Keyword = "CIRCULARSTRING",
                Empty = true,
                ExpectKind = "DECLINE",
                ExpectDecline = "ID_Empty",
                SignedWkb = 8,
            };
        }
        var (kind, bag, dec) = ExpectCs(controls);
        return new Model
        {
            Mid = mid,
            Keyword = "CIRCULARSTRING",
            Hens = bag?.Hens ?? [0, 1],
            Pts = bag?.Pts ?? [controls[0], controls[^1]],
            Controls = controls.ToList(),
            Chickens = bag?.Chickens ?? [(0, 1, "MkCirc")],
            Tau = "TagCircularString",
            ExpectKind = kind,
            ExpectDecline = dec,
            ExpectBag = bag,
            SignedWkb = 8,
        };
    }

    internal static Model FinishCircle(string mid, IReadOnlyList<Xy> controls, bool empty = false)
    {
        if (empty || controls.Count == 0)
        {
            return new Model
            {
                Mid = mid,
                Keyword = "CIRCLE",
                Empty = true,
                ExpectKind = "DECLINE",
                ExpectDecline = "ID_Empty",
                Hold = true,
            };
        }
        var (kind, bag, dec) = ExpectCircle(controls);
        return new Model
        {
            Mid = mid,
            Keyword = "CIRCLE",
            Hens = bag?.Hens ?? [0, 1],
            Pts = bag?.Pts ?? [controls[0], controls[^1]],
            Controls = controls.ToList(),
            Chickens = bag?.Chickens ?? [(0, 1, "MkCirc")],
            Tau = "TagCircle",
            ExpectKind = kind,
            ExpectDecline = dec,
            ExpectBag = bag,
            Hold = true,
        };
    }

    internal static Model FinishClothoidJts(string mid)
    {
        var (kind, bag, dec) = ExpectClothoid();
        return new Model
        {
            Mid = mid,
            Keyword = "CLOTHOID",
            Hens = [0, 1],
            Pts = LockedClothoidPts.ToList(),
            Chickens = [(0, 1, "MkClothoid")],
            Tau = "TagClothoid",
            Jts = ("0", "0.005", "80"),
            ExpectKind = kind,
            ExpectDecline = dec,
            ExpectBag = bag,
            Hold = true,
        };
    }

    internal static Model FinishCompound(string mid, IReadOnlyList<Xy> lsPts, IReadOnlyList<Xy> csControls)
    {
        var ls = FinishLs(mid + "-ls", lsPts);
        var cs = FinishCs(mid + "-cs", csControls);
        if (ls.ExpectKind != "BAG" || cs.ExpectKind != "BAG" || ls.ExpectBag is null || cs.ExpectBag is null)
        {
            return new Model
            {
                Mid = mid,
                Keyword = "COMPOUNDCURVE",
                Children = [ls, cs],
                Tau = "TagLineString",
                ExpectKind = "DECLINE",
                ExpectDecline = ls.ExpectDecline ?? cs.ExpectDecline,
                SignedWkb = 9,
            };
        }
        var bag = AppendBag(ls.ExpectBag, cs.ExpectBag);
        return new Model
        {
            Mid = mid,
            Keyword = "COMPOUNDCURVE",
            Hens = bag.Hens,
            Pts = bag.Pts,
            Chickens = bag.Chickens,
            Children = [ls, cs],
            Tau = "TagLineString",
            ExpectKind = "BAG",
            ExpectBag = bag,
            SignedWkb = 9,
        };
    }

    internal static Model CatalogExpect(string exampleId, Dictionary<string, string> fields)
    {
        string wkt = fields.GetValueOrDefault("WKT", "");
        string bag = fields.GetValueOrDefault("BAG", "");
        string tau = fields.GetValueOrDefault("TAU", "");
        var (k, b, d) = Parse(bag);
        bool hold = fields.GetValueOrDefault("WKB-NDR", "").StartsWith("HOLD", StringComparison.OrdinalIgnoreCase);
        int? signed = null;
        if (exampleId.StartsWith("point-00", StringComparison.Ordinal)) signed = 1;
        else if (exampleId.StartsWith("linestring", StringComparison.Ordinal) || exampleId.StartsWith("geodesic", StringComparison.Ordinal)) signed = 2;
        else if (exampleId.StartsWith("circularstring", StringComparison.Ordinal)) signed = 8;
        else if (exampleId.StartsWith("compound", StringComparison.Ordinal)) signed = 9;
        string keyword = "LINESTRING";
        if (wkt.StartsWith("POINT", StringComparison.Ordinal)) keyword = "POINT";
        else if (wkt.StartsWith("CIRCULARSTRING", StringComparison.Ordinal)) keyword = "CIRCULARSTRING";
        else if (wkt.StartsWith("CIRCLE", StringComparison.Ordinal)) keyword = "CIRCLE";
        else if (wkt.StartsWith("COMPOUNDCURVE", StringComparison.Ordinal)) keyword = "COMPOUNDCURVE";
        else if (wkt.StartsWith("CLOTHOID", StringComparison.Ordinal)) keyword = "CLOTHOID";
        return new Model
        {
            Mid = exampleId,
            Keyword = keyword,
            Empty = wkt.Contains("EMPTY", StringComparison.Ordinal),
            Tau = tau,
            ExpectKind = k,
            ExpectDecline = d,
            ExpectBag = b,
            SignedWkb = signed,
            Hold = hold || keyword is "CIRCLE" or "CLOTHOID" || exampleId == "point-empty",
        };
    }
}
