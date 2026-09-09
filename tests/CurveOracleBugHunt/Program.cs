// CurveOracleBugHunt — differential NTS#857 curves vs Rocq oracle_bin
// Assisted-by: xAI Grok

using System.Diagnostics;
using System.Globalization;
using NetTopologySuite.Geometries;
using NetTopologySuite.Geometries.Curves;
using NetTopologySuite.IO;
using NetTopologySuite.Operation.Distance;

static class Program
{
    static int Main()
    {
        var gf = new GeometryFactory();
        var wkt = new WKTReader();
        int fails = 0, warns = 0, ok = 0;

        void Hit(string severity, string tag, string detail)
        {
            if (severity is "FAIL" or "BUG") fails++;
            else if (severity == "WARN") warns++;
            else ok++;
            Console.WriteLine($"{severity}\t{tag}\t{detail}");
        }

        static double Hyp(double x, double y) => Math.Sqrt(x * x + y * y);

        Console.WriteLine("=== ARC_LENGTH vs NTS CircularString.Length ===");
        foreach (var a in Cases.Arcs)
        {
            string stdin = $"ARC_LENGTH\n{a.Ax} {a.Ay}\n{a.Bx} {a.By}\n{a.Cx} {a.Cy}\n";
            string oOut;
            try { oOut = Oracle.Run(stdin); }
            catch (Exception ex) { Hit("FAIL", $"LEN/{a.Name}", $"oracle: {ex.Message}"); continue; }

            var cs = new CircularString(
                gf.CoordinateSequenceFactory.Create(new[]
                {
                    new Coordinate(a.Ax, a.Ay), new Coordinate(a.Bx, a.By), new Coordinate(a.Cx, a.Cy)
                }), gf);
            double ntsLen = cs.Length;
            double polyChord = Hyp(a.Bx - a.Ax, a.By - a.Ay) + Hyp(a.Cx - a.Bx, a.Cy - a.By);

            if (oOut is "DEGENERATE" or "NAN")
            {
                Hit("WARN", $"LEN/{a.Name}", $"oracle={oOut} nts_chord_len={ntsLen:G17}");
                continue;
            }

            double oracleLen = Oracle.ParseHexFloat(oOut);
            double rel = Math.Abs(ntsLen - oracleLen) / Math.Max(oracleLen, 1e-30);
            bool matchesPoly = Math.Abs(ntsLen - polyChord) < 1e-12;
            bool matchesOracle = rel < 1e-9;

            if (matchesOracle)
                Hit("OK", $"LEN/{a.Name}", $"nts={ntsLen:G17} oracle={oracleLen:G17}");
            else if (matchesPoly && oracleLen >= ntsLen - 1e-9)
                Hit("BUG", $"LEN/{a.Name}",
                    $"NTS Length is control-polyline={ntsLen:G17}; oracle arc={oracleLen:G17}; " +
                    $"short_by={(oracleLen - ntsLen):G17} ({100 * (oracleLen - ntsLen) / oracleLen:F2}%)");
            else
                Hit("FAIL", $"LEN/{a.Name}", $"nts={ntsLen:G17} oracle={oracleLen:G17} poly={polyChord:G17}");
        }

        Console.WriteLine("=== ENVELOPE (control bbox vs arc bulge) ===");
        {
            static double Deg(double d) => d * Math.PI / 180;
            double a2x = Math.Cos(Deg(-30)), a2y = Math.Sin(Deg(-30));
            double b2x = Math.Cos(Deg(10)), b2y = Math.Sin(Deg(10));
            double c2x = Math.Cos(Deg(50)), c2y = Math.Sin(Deg(50));
            var cs2 = new CircularString(gf.CoordinateSequenceFactory.Create(new[]
            {
                new Coordinate(a2x, a2y), new Coordinate(b2x, b2y), new Coordinate(c2x, c2y)
            }), gf);
            try
            {
                var env2 = cs2.EnvelopeInternal;
                const double trueMaxX = 1.0; // angle 0° on unit circle lies on arc
                if (env2.MaxX + 1e-12 < trueMaxX)
                    Hit("BUG", "ENV/axis_extreme",
                        $"control-point envelope MaxX={env2.MaxX:G17} < true arc MaxX={trueMaxX:G17} " +
                        $"(unit circle arc −30°…50°; GEOS uses analytical envelope)");
                else
                    Hit("OK", "ENV/axis_extreme", $"MaxX={env2.MaxX:G17}");
            }
            catch (NotSupportedException)
            {
                // Honest decline, not a wrong answer: arc-aware Envelope is
                // Proofs #615 ticket 615-e; this WARN flips when it lands.
                Hit("WARN", "ENV/axis_extreme", "NTS Envelope fail-closed (pending 615-e)");
            }
        }

        Console.WriteLine("=== ARC_DISTANCE vs NTS Distance(Point, CircularString) ===");
        foreach (var q in Cases.DistQueries)
        {
            var a = Cases.Arcs[q.ArcIdx];
            string stdin = $"ARC_DISTANCE\n{a.Ax} {a.Ay}\n{a.Bx} {a.By}\n{a.Cx} {a.Cy}\n{q.Px} {q.Py}\n";
            string oOut;
            try { oOut = Oracle.Run(stdin); }
            catch (Exception ex) { Hit("FAIL", $"DIST/{q.Name}", $"oracle: {ex.Message}"); continue; }

            var cs = new CircularString(gf.CoordinateSequenceFactory.Create(new[]
            {
                new Coordinate(a.Ax, a.Ay), new Coordinate(a.Bx, a.By), new Coordinate(a.Cx, a.Cy)
            }), gf);
            var pt = gf.CreatePoint(new Coordinate(q.Px, q.Py));
            double ntsDist;
            try
            {
                ntsDist = DistanceOp.Distance(pt, cs);
            }
            catch (NotSupportedException)
            {
                // Honest decline, not a wrong answer: arc-aware Distance is
                // Proofs #615 ticket 615-f; these WARNs flip when it lands.
                Hit("WARN", $"DIST/{q.Name}", "NTS DistanceOp fail-closed (pending 615-f)");
                continue;
            }

            if (oOut is "DEGENERATE" or "NAN")
            {
                Hit("WARN", $"DIST/{q.Name}", $"oracle={oOut} nts={ntsDist:G17}");
                continue;
            }
            double oracleDist = Oracle.ParseHexFloat(oOut);
            double abs = Math.Abs(ntsDist - oracleDist);
            double rel = abs / Math.Max(oracleDist, 1e-30);
            if (abs < 1e-9 || (oracleDist > 1e-9 && rel < 1e-9))
                Hit("OK", $"DIST/{q.Name}", $"nts={ntsDist:G17} oracle={oracleDist:G17}");
            else
                Hit("BUG", $"DIST/{q.Name}",
                    $"nts={ntsDist:G17} oracle={oracleDist:G17} abs={abs:G17} (chord DistanceOp)");
        }

        Console.WriteLine("=== LENGTH_UNIFIED golden vectors (615-d) ===");
        // NTS exact Length (arc locus, r·θ; ISO/IEC 13249-3 §7.3.1 Desc 8)
        // against the oracle's LENGTH_UNIFIED lane, on the same cases the
        // NUnit contracts pin (CurveMetricsTests). Segments: "C x1 y1 x2 y2"
        // chord, "A x1 y1 x2 y2 x3 y3" 3-point arc.
        foreach (var v in Cases.LengthUnified)
        {
            string stdin = $"LENGTH_UNIFIED\n{v.Segs.Length}\n" + string.Join("\n", v.Segs) + "\n";
            string oOut;
            try { oOut = Oracle.Run(stdin); }
            catch (Exception ex) { Hit("FAIL", $"LENU/{v.Name}", $"oracle: {ex.Message}"); continue; }

            string firstLine = oOut.Split('\n')[0].Trim();
            if (firstLine is "DEGENERATE" or "NAN")
            {
                Hit("WARN", $"LENU/{v.Name}", $"oracle={firstLine}");
                continue;
            }
            double oracleLen = Oracle.ParseHexFloat(firstLine);
            double ntsLen = v.Geometry(gf).Length;
            double rel = Math.Abs(ntsLen - oracleLen) / Math.Max(Math.Abs(oracleLen), 1e-30);
            if (rel < 1e-9 || Math.Abs(ntsLen - oracleLen) < 1e-12)
                Hit("OK", $"LENU/{v.Name}", $"nts={ntsLen:G17} oracle={oracleLen:G17}");
            else
                Hit("BUG", $"LENU/{v.Name}", $"nts={ntsLen:G17} oracle={oracleLen:G17} rel={rel:G6}");
        }

        Console.WriteLine("=== ENVELOPE_UNIFIED golden vectors (615-e) ===");
        // NTS exact envelope (arc locus, §5.1.19 Desc 2b: endpoints + centre±r
        // on crossed axis directions) against the oracle's ENVELOPE_UNIFIED
        // lane (exact-Q crossing decisions, one float step on the extremes).
        foreach (var v in Cases.EnvelopeUnified)
        {
            string stdin = $"ENVELOPE_UNIFIED\n{v.Segs.Length}\n" + string.Join("\n", v.Segs) + "\n";
            string oOut;
            try { oOut = Oracle.Run(stdin); }
            catch (Exception ex) { Hit("FAIL", $"ENVU/{v.Name}", $"oracle: {ex.Message}"); continue; }

            if (oOut is "NAN" or "EMPTY")
            {
                Hit("WARN", $"ENVU/{v.Name}", $"oracle={oOut}");
                continue;
            }
            string[] parts = oOut.Split(' ', StringSplitOptions.RemoveEmptyEntries);
            if (parts.Length != 4)
            {
                Hit("FAIL", $"ENVU/{v.Name}", $"unexpected oracle output: {oOut}");
                continue;
            }
            var env = v.Geometry(gf).EnvelopeInternal;
            double[] nts = { env.MinX, env.MinY, env.MaxX, env.MaxY };
            string[] side = { "minx", "miny", "maxx", "maxy" };
            bool allOk = true;
            for (int i = 0; i < 4; i++)
            {
                double o = Oracle.ParseHexFloat(parts[i]);
                double abs = Math.Abs(nts[i] - o);
                double rel = abs / Math.Max(Math.Abs(o), 1e-30);
                if (abs > 1e-12 && rel > 1e-9)
                {
                    allOk = false;
                    Hit("BUG", $"ENVU/{v.Name}", $"{side[i]}: nts={nts[i]:G17} oracle={o:G17}");
                }
            }
            if (allOk)
                Hit("OK", $"ENVU/{v.Name}",
                    $"[{env.MinX:G17},{env.MinY:G17}]..[{env.MaxX:G17},{env.MaxY:G17}]");
        }

        Console.WriteLine("=== WKT/WKB structural ===");
        foreach (var s in new[]
        {
            "CIRCULARSTRING (0 0, 1 1, 2 0)",
            "COMPOUNDCURVE ((0 0, 1 0), CIRCULARSTRING (1 0, 2 1, 3 0))",
            "CURVEPOLYGON (CIRCULARSTRING (0 0, 2 2, 4 0, 2 -2, 0 0))",
            "MULTICURVE (CIRCULARSTRING (0 0, 1 1, 2 0), (3 0, 4 0))",
            "MULTISURFACE (CURVEPOLYGON (CIRCULARSTRING (0 0, 2 2, 4 0, 2 -2, 0 0)))",
        })
        {
            try
            {
                var g = wkt.Read(s);
                var bytes = new WKBWriter().Write(g);
                var g2 = new WKBReader().Read(bytes);
                if (!g2.EqualsExact(g))
                    Hit("BUG", "WKB/" + g.GeometryType, "EqualsExact failed after WKB round-trip");
                else
                    Hit("OK", "WKB/" + g.GeometryType, "round-trip");
            }
            catch (Exception ex)
            {
                Hit("FAIL", "WKB/" + s.Split(' ')[0], ex.Message);
            }
        }

        Console.WriteLine("=== RELATE_MATRIX token allowlist (no oracle) ===");
        {
            try
            {
                var (kind, val) = Oracle.ParseRelateWire("UNSUPPORTED");
                if (kind == "token" && val == "UNSUPPORTED")
                    Hit("OK", "REL/token_unsupported", "decline is a token, not a parse error");
                else
                    Hit("FAIL", "REL/token_unsupported", $"got {kind} {val}");
            }
            catch (Exception ex) { Hit("FAIL", "REL/token_unsupported", ex.Message); }

            try
            {
                var (kind, val) = Oracle.ParseRelateWire("FFFFFFFFF");
                if (kind == "matrix" && val == "FFFFFFFFF")
                    Hit("OK", "REL/matrix_disjoint_pin",
                        "#530 / #571 sentinel is a matrix, not UNSUPPORTED");
                else
                    Hit("FAIL", "REL/matrix_disjoint_pin", $"got {kind} {val}");
            }
            catch (Exception ex) { Hit("FAIL", "REL/matrix_disjoint_pin", ex.Message); }

            try
            {
                Oracle.ParseRelateWire("NOT_A_TOKEN");
                Hit("FAIL", "REL/unknown_rejected", "unknown token was accepted");
            }
            catch (Exception)
            {
                Hit("OK", "REL/unknown_rejected", "unknown token is still a parse error");
            }

            try
            {
                var (kind, val) = Oracle.ParseRelateWire("FF?FF1212");
                if (kind == "matrix" && val == "FF?FF1212")
                    Hit("OK", "REL/matrix_cell_unknown",
                        "? is a matrix cell, not a third parse kind (523-b)");
                else
                    Hit("FAIL", "REL/matrix_cell_unknown", $"got {kind} {val}");
            }
            catch (Exception ex) { Hit("FAIL", "REL/matrix_cell_unknown", ex.Message); }

            try
            {
                Oracle.ParseRelateWire("?");
                Hit("FAIL", "REL/bare_unknown_rejected", "bare ? was accepted as Decline");
            }
            catch (Exception)
            {
                Hit("OK", "REL/bare_unknown_rejected",
                    "bare ? is not Decline and not RELATE_TOKENS");
            }
        }

        Console.WriteLine("=== RELATE_MATRIX golden vectors (oracle catalog; #575 / 522-f) ===");
        foreach (var v in Cases.RelateVectors)
        {
            string oOut;
            try { oOut = Oracle.Run($"RELATE_MATRIX\n{v.Key}\n"); }
            catch (Exception ex)
            {
                Hit("WARN", $"REL/{v.Tag}", $"oracle missing or failed: {ex.Message}");
                continue;
            }
            try
            {
                var (kind, val) = Oracle.ParseRelateWire(oOut);
                if (kind == v.Kind && val == v.Expected)
                    Hit("OK", $"REL/{v.Tag}", $"{v.Key} -> {kind} {val} ({v.Provenance})");
                else
                    Hit("FAIL", $"REL/{v.Tag}",
                        $"{v.Key} -> {kind} {val} (exp {v.Kind} {v.Expected}); {v.Provenance}");
            }
            catch (Exception ex) { Hit("FAIL", $"REL/{v.Tag}", ex.Message); }
        }

        Console.WriteLine("=== chord_le_arc_length (oracle theorem) ===");
        foreach (var a in Cases.Arcs)
        {
            string oOut = Oracle.Run($"ARC_LENGTH\n{a.Ax} {a.Ay}\n{a.Bx} {a.By}\n{a.Cx} {a.Cy}\n");
            if (oOut is "DEGENERATE" or "NAN") continue;
            double oracleLen = Oracle.ParseHexFloat(oOut);
            double endChord = Hyp(a.Cx - a.Ax, a.Cy - a.Ay);
            if (endChord > oracleLen + 1e-9)
                Hit("FAIL", $"INVAR/{a.Name}", $"endChord {endChord} > arc {oracleLen}");
            else
                Hit("OK", $"INVAR/chord_le_arc/{a.Name}", $"chord={endChord:G9} arc={oracleLen:G9}");
        }

        Console.WriteLine("=== RING_SIMPLE vs NTS IsSimple rung 1 (615-h / #624) ===");
        // Single-segment simplicity is decided on the branch (arc: injective
        // sweep; collinear: the Desc-8b chord — sent to the oracle AS a chord,
        // since the RING_SIMPLE lane's arc parser requires a circumcentre and
        // answers DEGENERATE for collinear controls). The multi-segment case
        // is the fail-closed frontier (Proofs #630): the oracle decides it,
        // NTS must throw — both sides of that contract are pinned here.
        foreach (var v in Cases.RingSimple)
        {
            string stdin = $"RING_SIMPLE\n{v.Segs.Length}\n" + string.Join("\n", v.Segs) + "\n";
            string oOut;
            try { oOut = Oracle.Run(stdin); }
            catch (Exception ex) { Hit("FAIL", $"SIMPLE/{v.Name}", $"oracle: {ex.Message}"); continue; }

            string oVerdict = oOut.Split(' ')[0];
            if (oVerdict != v.OracleExpected)
            {
                Hit("FAIL", $"SIMPLE/{v.Name}", $"oracle={oOut} (exp {v.OracleExpected})");
                continue;
            }

            var g = v.Geometry(gf);
            bool? nts;
            try { nts = g.IsSimple; }
            catch (NotSupportedException) { nts = null; }

            if (v.NtsExpected is bool expected)
            {
                if (nts == expected)
                    Hit("OK", $"SIMPLE/{v.Name}", $"oracle={oOut} nts={nts}");
                else
                    Hit("BUG", $"SIMPLE/{v.Name}", $"oracle={oOut} nts={(object?)nts ?? "throw"} (exp {expected})");
            }
            else
            {
                // The frontier contract: the oracle decides, NTS stays
                // fail-closed until the arc-arc rung (#630) lands.
                if (nts is null)
                    Hit("OK", $"SIMPLE/{v.Name}", $"oracle={oOut}; nts fail-closed (contract)");
                else
                    Hit("BUG", $"SIMPLE/{v.Name}",
                        $"oracle={oOut}; nts answered {nts} but this row's contract is fail-closed");
            }
        }

        Console.WriteLine();
        Console.WriteLine($"SUMMARY\tok={ok}\twarn={warns}\tbug_or_fail={fails}");
        return fails > 0 ? 1 : 0;
    }
}

static class Oracle
{
    public static string Run(string modeInput)
    {
        // Same contract as tests/GeosOracleBugHunt/hunt.py: ORACLE overrides.
        // On Windows the default is the downloaded CI artifact run through WSL;
        // elsewhere the in-repo build (`make -C oracle`), resolved from the
        // repo root -- run via `dotnet run --project tests/CurveOracleBugHunt`
        // from the root, or set ORACLE.
        string bin = Environment.GetEnvironmentVariable("ORACLE")
            ?? (OperatingSystem.IsWindows()
                ? "/mnt/c/com/github/grootstebozewolf/NetTopologySuite.Proofs/.ci-artifacts/oracle-bin-linux/oracle_bin"
                : "oracle/oracle_bin");
        var psi = OperatingSystem.IsWindows()
            ? new ProcessStartInfo
            {
                FileName = "wsl",
                Arguments = "-e " + bin,
                RedirectStandardInput = true,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
            }
            : new ProcessStartInfo
            {
                FileName = bin,
                RedirectStandardInput = true,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
            };
        using var p = Process.Start(psi)!;
        p.StandardInput.Write(modeInput);
        p.StandardInput.Close();
        string stdout = p.StandardOutput.ReadToEnd().Trim();
        string stderr = p.StandardError.ReadToEnd();
        if (!p.WaitForExit(20000))
            throw new Exception("oracle timeout");
        if (p.ExitCode != 0 && string.IsNullOrEmpty(stdout))
            throw new Exception($"oracle exit {p.ExitCode}: {stderr}");
        return stdout;
    }

    /// <summary>
    /// Classify one RELATE_MATRIX oracle line.
    /// <c>UNSUPPORTED</c> is a decline (result position only), not a parse error.
    /// </summary>
    public static (string Kind, string Value) ParseRelateWire(string s)
    {
        string t = s.Trim();
        if (t == "UNSUPPORTED")
            return ("token", t);
        if (t.Length == 9 && t.All(c => c is 'F' or '0' or '1' or '2' or '?'))
            return ("matrix", t);
        throw new Exception(
            $"relate wire: not a 9-char matrix and not an allowlisted token: '{t}'");
    }

    public static double ParseHexFloat(string s)
    {
        if (s is "DEGENERATE" or "NAN") return double.NaN;
        s = s.Trim();
        bool neg = s.StartsWith('-');
        if (neg) s = s[1..];
        if (!s.StartsWith("0x", StringComparison.OrdinalIgnoreCase))
            return double.Parse(s, CultureInfo.InvariantCulture);
        s = s[2..];
        int p = s.IndexOf('p', StringComparison.OrdinalIgnoreCase);
        if (p < 0)
        {
            double v0 = Convert.ToInt64(s, 16);
            return neg ? -v0 : v0;
        }
        string mant = s[..p];
        int exp = int.Parse(s[(p + 1)..], CultureInfo.InvariantCulture);
        double m;
        int dot = mant.IndexOf('.');
        if (dot < 0)
            m = Convert.ToInt64(mant, 16);
        else
        {
            string whole = mant[..dot];
            string frac = mant[(dot + 1)..];
            m = whole.Length == 0 ? 0 : Convert.ToInt64(whole, 16);
            double f = 0;
            for (int i = 0; i < frac.Length; i++)
            {
                int d = Convert.ToInt32(frac.Substring(i, 1), 16);
                f = f * 16 + d;
            }
            m += f / Math.Pow(16, frac.Length);
        }
        double v = m * Math.Pow(2, exp);
        return neg ? -v : v;
    }
}

static class Cases
{
    public static readonly (string Name, double Ax, double Ay, double Bx, double By, double Cx, double Cy)[] Arcs =
    {
        ("unit_quarter", 1, 0, 0.7071067811865476, 0.7071067811865476, 0, 1),
        ("unit_semicircle", 1, 0, 0, 1, -1, 0),
        ("unit_lower_semi", 1, 0, 0, -1, -1, 0),
        ("R5_semi", 5, 0, 0, 5, -5, 0),
        ("flat_almost_chord", 0, 0, 5, 0.01, 10, 0),
        ("off_centre", 3, 4, 5, 4, 4, 5),
        ("tiny_arc", 0, 0, 1e-3, 1e-6, 2e-3, 0),
    };

    /// <summary>
    /// LENGTH_UNIFIED golden vectors (Proofs #615 ticket 615-d): oracle segment
    /// lines paired with the NTS geometry whose exact <c>Length</c> must agree.
    /// Mirrors the NUnit contracts in the fork's <c>CurveMetricsTests</c>.
    /// </summary>
    public static readonly (string Name, string[] Segs, Func<GeometryFactory, Geometry> Geometry)[] LengthUnified =
    {
        ("unit_semicircle", new[] { "A 1 0 0 1 -1 0" },
            gf => Cs(gf, (1, 0), (0, 1), (-1, 0))),
        ("major_arc_3pi_over_2", new[] { "A 1 0 0 1 0 -1" },
            gf => Cs(gf, (1, 0), (0, 1), (0, -1))),
        ("cw_semicircle_witness", new[] { "A -1 0 0 1 1 0" },
            gf => Cs(gf, (-1, 0), (0, 1), (1, 0))),
        ("multiseg_unequal_radii", new[] { "A 0 0 1 1 2 0", "A 2 0 4 2 6 0" },
            gf => Cs(gf, (0, 0), (1, 1), (2, 0), (4, 2), (6, 0))),
        ("collinear_chord", new[] { "A 0 0 1 1 2 2" },
            gf => Cs(gf, (0, 0), (1, 1), (2, 2))),
        ("full_circle_5pt", new[] { "A 0 0 1 1 2 0", "A 2 0 1 -1 0 0" },
            gf => Cs(gf, (0, 0), (1, 1), (2, 0), (1, -1), (0, 0))),
        ("compound_line_plus_semi", new[] { "C 0 0 1 0", "A 1 0 2 1 3 0" },
            gf => new CompoundCurve(new Curve[]
            {
                gf.CreateLineString(new[] { new Coordinate(0, 0), new Coordinate(1, 0) }),
                Cs(gf, (1, 0), (2, 1), (3, 0)),
            }, gf)),
    };

    /// <summary>
    /// RING_SIMPLE vectors (Proofs #615 ticket 615-h, #624 rung 1).
    /// OracleExpected is the verdict's first token (SIMPLE / NOT_SIMPLE /
    /// DEGENERATE). NtsExpected: a bool for a decided IsSimple, null for the
    /// fail-closed contract (NTS must throw NotSupportedException).
    /// The degenerate closed single segment (start == end) is a THROW row:
    /// the e00c00b endpoint-equality check runs before any float orientation
    /// step but only routes that triple to the fail-closed throw — NTS
    /// returns no verdict for it, matching the oracle's own DEGENERATE
    /// decline. A collinear single segment is sent to the oracle AS its
    /// Desc-8b chord ("C ..."): the lane's arc parser needs a circumcentre
    /// and calls collinear arc controls DEGENERATE, while NTS reads them as
    /// the chord. The bowtie is a classical LineString ring — a chord-only
    /// NOT_SIMPLE protocol pin, not a curve-locus simplicity claim.
    /// </summary>
    public static readonly (string Name, string[] Segs, string OracleExpected, bool? NtsExpected, Func<GeometryFactory, Geometry> Geometry)[] RingSimple =
    {
        ("single_arc_semicircle", new[] { "A 1 0 0 1 -1 0" }, "SIMPLE", true,
            gf => Cs(gf, (1, 0), (0, 1), (-1, 0))),
        ("single_arc_major", new[] { "A 1 0 0 1 0 -1" }, "SIMPLE", true,
            gf => Cs(gf, (1, 0), (0, 1), (0, -1))),
        ("single_collinear_as_chord", new[] { "C 0 0 2 2" }, "SIMPLE", true,
            gf => Cs(gf, (0, 0), (1, 1), (2, 2))),
        ("single_degenerate_closed", new[] { "A 1 0 0 1 1 0" }, "DEGENERATE", null,
            gf => Cs(gf, (1, 0), (0, 1), (1, 0))),
        ("two_arcs_tangent_at_vertex", new[] { "A 0 0 1 1 2 0", "A 2 0 3 -1 4 0" }, "SIMPLE", null,
            gf => Cs(gf, (0, 0), (1, 1), (2, 0), (3, -1), (4, 0))),
        ("bowtie_4chords", new[] { "C 0 0 2 2", "C 2 2 2 0", "C 2 0 0 2", "C 0 2 0 0" }, "NOT_SIMPLE", false,
            gf => gf.CreateLineString(new[]
            {
                new Coordinate(0, 0), new Coordinate(2, 2), new Coordinate(2, 0),
                new Coordinate(0, 2), new Coordinate(0, 0),
            })),
    };

    /// <summary>
    /// ENVELOPE_UNIFIED golden vectors (Proofs #615 ticket 615-e), mirroring
    /// the fork's CurveMetricsTests envelope contracts.
    /// </summary>
    public static readonly (string Name, string[] Segs, Func<GeometryFactory, Geometry> Geometry)[] EnvelopeUnified =
        BuildEnvelopeUnified();

    private static (string, string[], Func<GeometryFactory, Geometry>)[] BuildEnvelopeUnified()
    {
        static double Rad(double d) => d * Math.PI / 180.0;
        static string A(params double[] v) =>
            "A " + string.Join(" ", v.Select(d => d.ToString("R", CultureInfo.InvariantCulture)));
        double[] axisArc =
        {
            Math.Cos(Rad(-30)), Math.Sin(Rad(-30)),
            Math.Cos(Rad(10)), Math.Sin(Rad(10)),
            Math.Cos(Rad(50)), Math.Sin(Rad(50)),
        };
        return new (string, string[], Func<GeometryFactory, Geometry>)[]
        {
            ("axis_extreme_-30_50", new[] { A(axisArc) },
                gf => Cs(gf, (axisArc[0], axisArc[1]), (axisArc[2], axisArc[3]), (axisArc[4], axisArc[5]))),
            ("collinear_excludes_intermediate", new[] { "A 0 0 5 5 2 2" },
                gf => Cs(gf, (0, 0), (5, 5), (2, 2))),
            ("full_circle_5pt", new[] { "A 0 0 1 1 2 0", "A 2 0 1 -1 0 0" },
                gf => Cs(gf, (0, 0), (1, 1), (2, 0), (1, -1), (0, 0))),
            ("cw_major_arc_bulge", new[] { "A 0 0 5 10 10 0" },
                gf => Cs(gf, (0, 0), (5, 10), (10, 0))),
            ("compound_line_plus_arc", new[] { "C -3 0 1 0", "A 1 0 2 1 3 0" },
                gf => new CompoundCurve(new Curve[]
                {
                    gf.CreateLineString(new[] { new Coordinate(-3, 0), new Coordinate(1, 0) }),
                    Cs(gf, (1, 0), (2, 1), (3, 0)),
                }, gf)),
        };
    }

    private static CircularString Cs(GeometryFactory gf, params (double x, double y)[] pts)
    {
        var coords = new Coordinate[pts.Length];
        for (int i = 0; i < pts.Length; i++) coords[i] = new Coordinate(pts[i].x, pts[i].y);
        return new CircularString(gf.CoordinateSequenceFactory.Create(coords), gf);
    }

    public static readonly (string Name, int ArcIdx, double Px, double Py)[] DistQueries =
    {
        ("semi_center", 1, 0, 0),
        ("semi_outside", 1, 0, 2),
        ("semi_endpoint", 1, 1, 0),
        ("semi_off_sweep", 1, 0, -2),
        ("quarter_origin", 0, 0, 0),
        ("quarter_inside", 0, 0.5, 0.5),
    };

    // Classifier pins from oracle/de9im_triangle_vectors.txt. Not OGC remints.
    // #530 is DISJOINT, not the decline. Decline is an unnamed CCW pair.
    // Leftover Ⅵ classifies same-cone (fill still UNSUPPORTED).
    // Leftover Ⅴ classifies mixed-cone (fill still UNSUPPORTED).
    // Leftover Ⅱ classifies obtuse-at-v (fill still UNSUPPORTED).
    // The T-junction pair classifies leftover Ⅰ (fill still UNSUPPORTED).
    public static readonly (string Tag, string Key, string Kind, string Expected, string Provenance)[] RelateVectors =
    {
        ("DISJOINT", "triangle_pair_fill TPR_Disjoint", "matrix", "FFFFFFFFF",
            "#571 / 522-c sentinel (the #530 pair, now classified)"),
        ("OVERLAP", "triangle_pair_fill TPR_Overlap", "matrix", "2FFF1FFF2",
            "#567 / 522-b overlap pair"),
        ("CONTAINS", "triangle_pair_fill TPR_Contains", "matrix", "2FFFFFFF2",
            "RelateMatrixTriangle.contains_pair_contains"),
        ("TOUCH_EDGE", "triangle_pair_fill TPR_TouchEdge", "matrix", "FFFF1FFF2",
            "frozen shared-edge pin"),
        ("TOUCH_VERTEX", "triangle_pair_fill TPR_TouchVertex", "matrix", "FFFF1FFF2",
            "#572 / 522-i pair"),
        ("TOUCH_PARTIAL", "triangle_pair_fill TPR_TouchPartialEdge", "token", "UNSUPPORTED",
            "Leftover Ⅰ kiss. Classified; fill not named."),
        ("TOUCH_OBTUSE", "triangle_pair_fill TPR_TouchObtuse", "token", "UNSUPPORTED",
            "Leftover Ⅱ obtuse-at-v. Classified; fill not named."),
        ("TOUCH_MIXED", "triangle_pair_fill TPR_MixedCone", "token", "UNSUPPORTED",
            "Leftover Ⅴ mixed-cone. Classified; fill not named."),
        ("SAME_CONE", "triangle_pair_fill TPR_SameCone", "token", "UNSUPPORTED",
            "Leftover Ⅵ same-cone. Classified; fill not named."),
        ("DECLINE", "triangle_pair_fill TPR_Unsupported", "token", "UNSUPPORTED",
            "Unnamed lens pair. Leftover Ⅵ classifies same-cone."),
    };
}
