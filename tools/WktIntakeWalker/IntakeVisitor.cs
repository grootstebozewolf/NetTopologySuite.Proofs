// ANTLR visitor: tagged CST → first-slice SHC bag | named Intake Decline.
// Mapping table is the same as theories/IntakeWalker.v.
// No noding, no split(t), no snap, no silent chord demote.
// Assisted-by: Cursor Grok 4.6. claimId: none (tools).

using System.Globalization;
using Antlr4.Runtime.Misc;
using Nts.Proofs.Intake.Gen;

namespace Nts.Proofs.Intake;

sealed class IntakeVisitor : wktParserBaseVisitor<IntakeResult>
{
    static readonly Pt P50 = new(5, 0);
    static readonly Pt P05 = new(0, 5);
    static readonly Pt PM50 = new(-5, 0);

    protected override IntakeResult DefaultResult => IntakeResult.OfDecline(Reason.ID_NotFirstSlice);

    protected override IntakeResult AggregateResult(IntakeResult aggregate, IntakeResult nextResult)
    {
        if (nextResult != null && (aggregate == null || !aggregate.IsBag
                && nextResult.Decline != Reason.ID_NotFirstSlice))
            return nextResult;
        return aggregate ?? DefaultResult;
    }

    public override IntakeResult VisitFile_([NotNull] wktParser.File_Context ctx)
    {
        var geoms = ctx.geometry();
        if (geoms.Length == 0)
            return IntakeResult.OfDecline(Reason.ID_Empty);
        if (geoms.Length != 1)
            return IntakeResult.OfDecline(Reason.ID_NotFirstSlice);
        return Visit(geoms[0]);
    }

    public override IntakeResult VisitPointGeometry([NotNull] wktParser.PointGeometryContext ctx)
    {
        if (ctx.dim() != null)
            return IntakeResult.OfDecline(Reason.ID_NotFirstSlice);
        if (ctx.pointText().EMPTY_() != null || ctx.pointText().point() == null)
            return IntakeResult.OfDecline(Reason.ID_Empty);
        var pts = PointsOf(ctx.pointText().point());
        if (pts.Count == 0)
            return IntakeResult.OfDecline(Reason.ID_Empty);
        return IntakeResult.OfBag(new Bag([0], pts, []));
    }

    public override IntakeResult VisitLineStringGeometry([NotNull] wktParser.LineStringGeometryContext ctx)
    {
        if (ctx.dim() != null)
            return IntakeResult.OfDecline(Reason.ID_NotFirstSlice);
        return MapLineString(PointsOf(ctx.lineStringText()));
    }

    public override IntakeResult VisitCircularStringGeometry([NotNull] wktParser.CircularStringGeometryContext ctx)
    {
        if (ctx.dim() != null)
            return IntakeResult.OfDecline(Reason.ID_NotFirstSlice);
        return MapCircularString(PointsOf(ctx.lineStringText()));
    }

    public override IntakeResult VisitCircleGeometry([NotNull] wktParser.CircleGeometryContext ctx)
    {
        if (ctx.dim() != null)
            return IntakeResult.OfDecline(Reason.ID_NotFirstSlice);
        return MapCircle(PointsOf(ctx.lineStringText()));
    }

    public override IntakeResult VisitCompoundCurveGeometry([NotNull] wktParser.CompoundCurveGeometryContext ctx)
    {
        if (ctx.dim() != null)
            return IntakeResult.OfDecline(Reason.ID_NotFirstSlice);
        if (ctx.EMPTY_() != null || ctx.compoundCurveMember().Length == 0)
            return IntakeResult.OfDecline(Reason.ID_Empty);
        IntakeResult? acc = null;
        IntakeResult? firstDecline = null;
        foreach (var member in ctx.compoundCurveMember())
        {
            var next = Visit(member.curveMember());
            if (!next.IsBag)
            {
                firstDecline ??= next;
                continue;
            }
            acc = acc == null ? next : IntakeResult.OfBag(Append(acc.Bag!, next.Bag!));
        }
        if (firstDecline != null)
            return firstDecline;
        return acc ?? IntakeResult.OfDecline(Reason.ID_Empty);
    }

    public override IntakeResult VisitCurveMember([NotNull] wktParser.CurveMemberContext ctx)
    {
        if (ctx.lineStringText() != null)
            return MapLineString(PointsOf(ctx.lineStringText()));
        if (ctx.circularStringGeometry() != null)
            return Visit(ctx.circularStringGeometry());
        if (ctx.circleGeometry() != null)
            return Visit(ctx.circleGeometry());
        if (ctx.geodesicStringGeometry() != null)
            return Visit(ctx.geodesicStringGeometry());
        if (ctx.clothoidGeometry() != null)
            return Visit(ctx.clothoidGeometry());
        if (ctx.spiralCurveGeometry() != null)
            return IntakeResult.OfDecline(Reason.ID_SpiralCurve);
        if (ctx.compoundCurveGeometry() != null)
            return Visit(ctx.compoundCurveGeometry());
        return IntakeResult.OfDecline(Reason.ID_NotFirstSlice);
    }

    public override IntakeResult VisitClothoidGeometry([NotNull] wktParser.ClothoidGeometryContext ctx)
    {
        var text = ctx.clothoidText();
        if (text.EMPTY_() != null)
            return IntakeResult.OfDecline(Reason.ID_Empty);
        return MapClothoid();
    }

    public override IntakeResult VisitGeodesicStringGeometry([NotNull] wktParser.GeodesicStringGeometryContext ctx)
    {
        if (ctx.dim() != null)
            return IntakeResult.OfDecline(Reason.ID_NotFirstSlice);
        return MapLineString(PointsOf(ctx.lineStringText()));
    }

    public override IntakeResult VisitSpiralCurveGeometry([NotNull] wktParser.SpiralCurveGeometryContext ctx)
    {
        return IntakeResult.OfDecline(Reason.ID_SpiralCurve);
    }

    public override IntakeResult VisitGeometry([NotNull] wktParser.GeometryContext ctx) => VisitChildren(ctx);

    internal static IntakeResult MapLineString(IReadOnlyList<Pt> pts)
    {
        if (pts.Count == 0)
            return IntakeResult.OfDecline(Reason.ID_Empty);
        if (pts.Count < 2)
            return IntakeResult.OfDecline(Reason.ID_BadPointCount);
        var chickens = new List<Chicken>();
        for (int i = 0; i < pts.Count - 1; i++)
            chickens.Add(new Chicken(i, i + 1, "MkChord"));
        return IntakeResult.OfBag(new Bag(Hens(pts.Count), pts, chickens));
    }

    internal static IntakeResult MapCircularString(IReadOnlyList<Pt> pts)
    {
        if (pts.Count == 0)
            return IntakeResult.OfDecline(Reason.ID_Empty);
        if (pts.Count == 3)
        {
            var a = pts[0];
            var c = pts[2];
            if (Eq(a, c))
                return IntakeResult.OfDecline(Reason.ID_CsClosedDegenerate);
            if (Eq(a, P50) && Eq(c, P05))
                return CircBag([P50, P05], "MkCirc:quarter");
        }
        return MapCsUnknown(pts);
    }

    internal static IntakeResult MapCircle(IReadOnlyList<Pt> pts)
    {
        if (pts.Count == 0)
            return IntakeResult.OfDecline(Reason.ID_Empty);
        if (pts.Count != 3)
            return IntakeResult.OfDecline(Reason.ID_BadPointCount);
        return MapCircleUnknown(pts);
    }

    /// <summary>Same table as theories/IntakeAngles.v try_cs_eggs.</summary>
    internal static IntakeResult MapCsUnknown(IReadOnlyList<Pt> pts)
    {
        if (pts.Count == 0)
            return IntakeResult.OfDecline(Reason.ID_Empty);
        if (pts.Count < 3 || pts.Count % 2 == 0)
            return IntakeResult.OfDecline(Reason.ID_BadPointCount);
        var ends = new List<Pt> { pts[0] };
        var chickens = new List<Chicken>();
        int hen = 0;
        for (int i = 0; i + 2 < pts.Count; i += 2)
        {
            var triple = TryTriple(pts[i], pts[i + 1], pts[i + 2]);
            if (!triple.IsBag)
                return triple;
            ends.Add(pts[i + 2]);
            chickens.Add(new Chicken(hen, hen + 1, "MkCirc"));
            hen++;
        }
        return IntakeResult.OfBag(new Bag(Hens(ends.Count), ends, chickens));
    }

    /// <summary>
    /// Same table as theories/IntakeAnglesCore.v try_circle_eggs.
    /// Two hens: A and the antipode 2O−A. Chickens 0→1 and 1→0, each sweep ±π.
    /// </summary>
    internal static IntakeResult MapCircleUnknown(IReadOnlyList<Pt> pts)
    {
        if (pts.Count == 0)
            return IntakeResult.OfDecline(Reason.ID_Empty);
        if (pts.Count != 3)
            return IntakeResult.OfDecline(Reason.ID_BadPointCount);
        var triple = TryTriple(pts[0], pts[1], pts[2]);
        if (!triple.IsBag)
            return triple;
        double d = CircDenom(pts[0], pts[1], pts[2]);
        var o = Circumcenter(pts[0], pts[1], pts[2], d);
        var anti = new Pt(2 * o.X - pts[0].X, 2 * o.Y - pts[0].Y);
        return IntakeResult.OfBag(new Bag(
            [0, 1],
            [pts[0], anti],
            [new Chicken(0, 1, "MkCirc:half"), new Chicken(1, 0, "MkCirc:half")]));
    }

    internal static IntakeResult TryTriple(Pt a, Pt b, Pt c)
    {
        if (Same(a, b) || Same(b, c) || Same(a, c))
            return IntakeResult.OfDecline(Reason.ID_DuplicateControl);
        double d = CircDenom(a, b, c);
        if (d == 0.0)
            return IntakeResult.OfDecline(Reason.ID_Collinear);
        var o = Circumcenter(a, b, c, d);
        double r2 = (a.X - o.X) * (a.X - o.X) + (a.Y - o.Y) * (a.Y - o.Y);
        if (r2 == 0.0)
            return IntakeResult.OfDecline(Reason.ID_DegenerateArc);
        return IntakeResult.OfBag(new Bag([], [], []));
    }

    internal static double CircDenom(Pt a, Pt b, Pt c) =>
        2 * (a.X * (b.Y - c.Y) + b.X * (c.Y - a.Y) + c.X * (a.Y - b.Y));

    internal static Pt Circumcenter(Pt a, Pt b, Pt c, double d)
    {
        double na = a.X * a.X + a.Y * a.Y;
        double nb = b.X * b.X + b.Y * b.Y;
        double nc = c.X * c.X + c.Y * c.Y;
        double ux = (na * (b.Y - c.Y) + nb * (c.Y - a.Y) + nc * (a.Y - b.Y)) / d;
        double uy = (na * (c.X - b.X) + nb * (a.X - c.X) + nc * (b.X - a.X)) / d;
        return new Pt(ux, uy);
    }

    static bool Same(Pt a, Pt b) => a.X == b.X && a.Y == b.Y;

    static IntakeResult CircBag(IReadOnlyList<Pt> pts, string egg) =>
        IntakeResult.OfBag(new Bag([0, 1], pts, [new Chicken(0, 1, egg)]));

    /// <summary>
    /// Same locked bag as theories/IntakeWalker.v map_clothoid.
    /// Vertices are γ(0), γ(1) of locked_clothoid_egg:
    /// k0=0, k1=5/1000, L=80, θ0=0 (small-angle clothoid, not chord-seed).
    /// γ(1) = (80, (k1-k0)·L²/6) = (80, 16/3).
    /// </summary>
    internal static IntakeResult MapClothoid()
    {
        double k1 = 5.0 / 1000.0;
        double L = 80.0;
        double y1 = (k1 - 0.0) * (L * L) / 6.0;
        return IntakeResult.OfBag(new Bag(
            [0, 1],
            [new Pt(0, 0), new Pt(L, y1)],
            [new Chicken(0, 1, "MkClothoid")]));
    }

    static Bag Append(Bag a, Bag b)
    {
        int off = a.Hens.Count;
        var hens = a.Hens.Concat(b.Hens.Select(h => off + h));
        var pts = a.Pts.Concat(b.Pts);
        var chickens = a.Chickens.Concat(
            b.Chickens.Select(c => new Chicken(off + c.Src, off + c.Dst, c.Egg)));
        return new Bag(hens, pts, chickens);
    }

    static List<int> Hens(int n) => Enumerable.Range(0, n).ToList();

    static List<Pt> PointsOf(wktParser.LineStringTextContext? ctx)
    {
        if (ctx == null || ctx.EMPTY_() != null)
            return [];
        return PointsOf(ctx.point());
    }

    static List<Pt> PointsOf(wktParser.PointContext? ctx) =>
        ctx == null ? [] : PointsOf([ctx]);

    static List<Pt> PointsOf(IReadOnlyList<wktParser.PointContext>? ctxs)
    {
        var pts = new List<Pt>();
        if (ctxs == null)
            return pts;
        foreach (var p in ctxs)
        {
            var ords = p.ordinate();
            if (ords.Length < 2)
                continue;
            pts.Add(new Pt(ParseOrd(ords[0]), ParseOrd(ords[1])));
        }
        return pts;
    }

    static double ParseOrd(wktParser.OrdinateContext ctx)
    {
        if (ctx.NAN_() != null)
            return double.NaN;
        if (ctx.INF_() != null)
            return double.PositiveInfinity;
        if (ctx.NEG_INF_() != null)
            return double.NegativeInfinity;
        return double.Parse(ctx.DECIMAL().GetText(), CultureInfo.InvariantCulture);
    }

    static bool Eq(Pt a, Pt b) => a.X == b.X && a.Y == b.Y;
}
