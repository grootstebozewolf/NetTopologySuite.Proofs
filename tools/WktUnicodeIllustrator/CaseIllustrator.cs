using NetTopologySuite.Geometries;

namespace WktUnicodeIllustrator;

/// <summary>
/// Pure entry for WKT pair Unicode case sketches (lines and SQL/MM curves).
/// Used by the CLI and by automated checks — same code path both ways.
/// Internally: <see cref="Compose"/> → <see cref="Scenario"/> →
/// <see cref="Style"/> → <see cref="Doc"/> → a printer (ANSI here).
/// </summary>
public static class CaseIllustrator
{
    public const string DefaultA = "LINESTRING (0 0, 10 10)";
    public const string DefaultB = "LINESTRING (0 10, 10 0)";

    /// <summary>Two arcs crossing near the middle of the square (curve demo).</summary>
    public const string DefaultCurveA = "CIRCULARSTRING (0 0, 5 8, 10 0)";
    public const string DefaultCurveB = "CIRCULARSTRING (0 10, 5 2, 10 10)";

    /// <summary>
    /// Self-overlapping circular string: second arc is the reverse of the first
    /// (same mid control) — full path retrace = overshoot / self-overlap.
    /// </summary>
    public const string DefaultOvershootA =
        "CIRCULARSTRING (0 0, 5 6, 10 0, 5 6, 0 0)";

    /// <summary>Companion self-overlapping arc for B (upper band, reverse retrace).</summary>
    public const string DefaultOvershootB =
        "CIRCULARSTRING (0 10, 5 4, 10 10, 5 4, 0 10)";

    /// <summary>Two heavily overlapping discs (Venn demo: ░ single, ╳ overlap).</summary>
    public const string DefaultVennA =
        "CURVEPOLYGON (CIRCULARSTRING (-1.4 0, -0.4 1, 0.6 0, -0.4 -1, -1.4 0))";

    /// <summary>Right disc of the Venn demo.</summary>
    public const string DefaultVennB =
        "CURVEPOLYGON (CIRCULARSTRING (-0.6 0, 0.4 1, 1.4 0, 0.4 -1, -0.6 0))";

    public static IllustratorResult Render(
        string? wktA = null,
        string? wktB = null,
        string operation = "intersection",
        int width = 41,
        int height = 21,
        bool useColor = false,
        bool showOvershoot = true,
        double cellAspect = WorldToGrid.DefaultCellAspect,
        bool showFill = true)
    {
        var composed = Compose(wktA, wktB, operation, width, height, showOvershoot, cellAspect, showFill);
        if (composed.Scenario is null)
            return IllustratorResult.Fail(composed.ExitCode, composed.Error!);

        var scenario = composed.Scenario;
        var doc = Style.Build(scenario, colored: useColor);

        return new IllustratorResult
        {
            ExitCode = 0,
            Text = AnsiPrinter.Print(doc),
            ResultWkt = scenario.Result is null ? null : scenario.Result.AsText(),
            ResultIsEmpty = scenario.Result?.IsEmpty ?? true,
            OvershootAWkt = scenario.OvershootA is { IsEmpty: false } oa ? oa.AsText() : null,
            OvershootBWkt = scenario.OvershootB is { IsEmpty: false } ob ? ob.AsText() : null,
        };
    }

    internal static ComposeResult Compose(
        string? wktA = null,
        string? wktB = null,
        string operation = "intersection",
        int width = 41,
        int height = 21,
        bool showOvershoot = true,
        double cellAspect = WorldToGrid.DefaultCellAspect,
        bool showFill = true)
    {
        wktA ??= DefaultA;
        wktB ??= DefaultB;

        // No chord fallback, by design: a lines-only build must never render a
        // curve case as its control chords — that picture lies.
        if (!GeometryCurves.HasCurveSupport
            && (GeometryCurves.ContainsCurveWkt(wktA) || GeometryCurves.ContainsCurveWkt(wktB)))
        {
            return ComposeResult.Fail(4,
                "Curve WKT requires the curve-aware NetTopologySuite clone; this build uses "
                + "NuGet NetTopologySuite (lines only). Clone NetTopologySuite (branch "
                + "feat/curves-metrics-followup) next to this repo or pass "
                + "-p:NtsProject=<path-to-NetTopologySuite.csproj>.");
        }

        Geometry a, b;
        try
        {
            a = GeometryCurves.Parse(wktA);
            b = GeometryCurves.Parse(wktB);
        }
        catch (Exception ex)
        {
            return ComposeResult.Fail(2, $"WKT parse failed: {ex.Message}");
        }

        if (a.IsEmpty || b.IsEmpty)
            return ComposeResult.Fail(2, "A and B must be non-empty geometries.");

        Geometry aDraw = GeometryCurves.Linearize(a);
        Geometry bDraw = GeometryCurves.Linearize(b);

        Geometry? overA = null;
        Geometry? overB = null;
        try
        {
            if (showOvershoot)
            {
                overA = Overshoot.ExtractSelfOverlap(a);
                overB = Overshoot.ExtractSelfOverlap(b);
            }
        }
        catch (Exception ex)
        {
            return ComposeResult.Fail(3, $"Overshoot extract failed: {ex.Message}");
        }

        var env = aDraw.EnvelopeInternal.Copy();
        env.ExpandToInclude(bDraw.EnvelopeInternal);
        if (overA is { IsEmpty: false }) env.ExpandToInclude(overA.EnvelopeInternal);
        if (overB is { IsEmpty: false }) env.ExpandToInclude(overB.EnvelopeInternal);

        // Self-overlapping densified curves are not overlay-safe; node segments first.
        Geometry aOp = Overshoot.PrepareForOverlay(aDraw);
        Geometry bOp = Overshoot.PrepareForOverlay(bDraw);

        Geometry? result;
        string opName = operation;
        try
        {
            result = operation.ToLowerInvariant() switch
            {
                "intersection" or "cross" or "x" => aOp.Intersection(bOp),
                "union" => aOp.Union(bOp),
                "difference" => aOp.Difference(bOp),
                "symdifference" or "xor" => aOp.SymmetricDifference(bOp),
                "none" => null,
                _ => aOp.Intersection(bOp),
            };
            if (operation is "cross" or "x")
                opName = "intersection";
            if (GeometryCurves.IsCurve(a) || GeometryCurves.IsCurve(b))
                opName += " (linearized curves)";
        }
        catch (Exception ex)
        {
            return ComposeResult.Fail(3, $"Operation failed: {ex.Message}");
        }

        if (result is { IsEmpty: false })
            env.ExpandToInclude(result.EnvelopeInternal);

        if (env.Width == 0) env.ExpandBy(1, 0);
        if (env.Height == 0) env.ExpandBy(0, 1);

        width = Math.Clamp(width, 8, 200);
        height = Math.Clamp(height, 4, 100);

        var map = new WorldToGrid(env, width, height, cellAspect: cellAspect);
        var canvas = new Canvas(width, height);

        Rasterizer.DrawGeometry(canvas, map, aDraw, Layer.A);
        Rasterizer.DrawGeometry(canvas, map, bDraw, Layer.B);
        if (showFill)
        {
            Rasterizer.FillGeometry(canvas, map, aDraw, Layer.FillA);
            Rasterizer.FillGeometry(canvas, map, bDraw, Layer.FillB);
        }
        if (overA is { IsEmpty: false })
            Rasterizer.DrawGeometry(canvas, map, overA, Layer.OvershootA);
        if (overB is { IsEmpty: false })
            Rasterizer.DrawGeometry(canvas, map, overB, Layer.OvershootB);
        if (result is { IsEmpty: false })
            Rasterizer.DrawGeometry(canvas, map, result, Layer.Result);

        return ComposeResult.Ok(new Scenario
        {
            A = a,
            B = b,
            Result = result,
            OvershootA = overA,
            OvershootB = overB,
            ShowOvershoot = showOvershoot,
            OpName = opName,
            Canvas = canvas,
            Map = map,
        });
    }
}

public sealed class IllustratorResult
{
    public int ExitCode { get; init; }
    public string Text { get; init; } = "";
    public string? ResultWkt { get; init; }
    public bool ResultIsEmpty { get; init; }
    public string? OvershootAWkt { get; init; }
    public string? OvershootBWkt { get; init; }
    public string? Error { get; init; }

    public static IllustratorResult Fail(int code, string error) =>
        new() { ExitCode = code, Error = error, Text = error + Environment.NewLine };
}
