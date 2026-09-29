// First-slice intake answer. Mirrors theories/IntakeWalker.v.
// Intake Decline is not cook IDecline. Wire format matches the retired Java visitor.
// Assisted-by: Cursor Grok 4.6. claimId: none (tools).

using System.Globalization;
using System.Text;

namespace Nts.Proofs.Intake;

enum Reason
{
    ID_Empty,
    ID_BadPointCount,
    ID_GeodesicString,
    ID_SpiralCurve,
    ID_IsoClothoid,
    ID_MkOutOfScope,
    ID_CircGammaLeftover,
    ID_Collinear,
    ID_DuplicateControl,
    ID_DegenerateArc,
    ID_CsClosedDegenerate,
    ID_NotFirstSlice,
    ID_ParseFail,
}

readonly record struct Pt(double X, double Y)
{
    public override string ToString() =>
        string.Create(CultureInfo.InvariantCulture, $"{IntakeResult.Trim(X)} {IntakeResult.Trim(Y)}");
}

readonly record struct Chicken(int Src, int Dst, string Egg)
{
    public override string ToString() => $"{Src}-{Dst}:{Egg}";
}

sealed class Bag
{
    public IReadOnlyList<int> Hens { get; }
    public IReadOnlyList<Pt> Pts { get; }
    public IReadOnlyList<Chicken> Chickens { get; }

    public Bag(IEnumerable<int> hens, IEnumerable<Pt> pts, IEnumerable<Chicken> chickens)
    {
        Hens = hens.ToList();
        Pts = pts.ToList();
        Chickens = chickens.ToList();
    }
}

sealed class IntakeResult
{
    public Bag? Bag { get; }
    public Reason? Decline { get; }

    IntakeResult(Bag? bag, Reason? decline)
    {
        Bag = bag;
        Decline = decline;
    }

    public static IntakeResult OfBag(Bag bag) => new(bag, null);
    public static IntakeResult OfDecline(Reason reason) => new(null, reason);
    public bool IsBag => Bag != null;

    public string Wire()
    {
        if (!IsBag)
            return "DECLINE " + Decline;
        var sb = new StringBuilder("BAG");
        sb.Append(" hens=");
        for (int i = 0; i < Bag!.Hens.Count; i++)
        {
            if (i > 0) sb.Append(',');
            sb.Append(Bag.Hens[i]);
        }
        sb.Append(" pts=");
        for (int i = 0; i < Bag.Pts.Count; i++)
        {
            if (i > 0) sb.Append(';');
            sb.Append(Bag.Pts[i]);
        }
        sb.Append(" chickens=");
        for (int i = 0; i < Bag.Chickens.Count; i++)
        {
            if (i > 0) sb.Append(',');
            sb.Append(Bag.Chickens[i]);
        }
        return sb.ToString();
    }

    /// <summary>
    /// Match java.lang.Double.toString + IntakeResult.trim for the bag wire.
    /// Integer-valued finite numbers inside 1e12 print as a long (Java Math.rint).
    /// </summary>
    internal static string Trim(double v)
    {
        if (double.IsNaN(v)) return "NaN";
        if (double.IsPositiveInfinity(v)) return "Infinity";
        if (double.IsNegativeInfinity(v)) return "-Infinity";
        if (v == Math.Round(v, MidpointRounding.ToEven) && Math.Abs(v) < 1e12)
            return ((long)v).ToString(CultureInfo.InvariantCulture);
        return JavaDoubleToString(v);
    }

    // Java Double.toString: shortest unique decimal (FloatingDecimal).
    // G17 + strip a trailing ".0" covers the first-slice smoke surface,
    // including locked clothoid y1 = 0.005·80²/6 → "5.333333333333333".
    static string JavaDoubleToString(double v)
    {
        string s = v.ToString("G17", CultureInfo.InvariantCulture);
        if (s.Contains('E', StringComparison.OrdinalIgnoreCase))
            return NormalizeJavaExp(s);
        if (s.EndsWith(".0", StringComparison.Ordinal) && s.Count(c => c == '.') == 1)
            return s[..^2];
        return s;
    }

    static string NormalizeJavaExp(string s)
    {
        // Java: "1.0E-4" style; C# G17 may emit "1E-04". First-slice bags
        // do not use this arm; keep a stable invariant form.
        return s.Replace("E+", "E", StringComparison.OrdinalIgnoreCase);
    }
}
