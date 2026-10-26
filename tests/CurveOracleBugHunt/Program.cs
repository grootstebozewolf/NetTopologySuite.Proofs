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

            if (Oracle.IsValidDe9imResult("FF?FF1212") && Oracle.IsValidDe9imResult("?????????"))
                Hit("OK", "REL/valid_result_unknown",
                    "IsValidDe9imResult accepts ? cells (523-b)");
            else
                Hit("FAIL", "REL/valid_result_unknown",
                    "IsValidDe9imResult rejected a 9-char with ?");

            if (Oracle.IsValidDe9imResult("?")
                || Oracle.IsValidDe9imResult("UNSUPPORTED")
                || Oracle.IsValidDe9imResult("FF0FF121T"))
                Hit("FAIL", "REL/valid_result_rejects",
                    "bare ? / token / pattern T treated as a result matrix");
            else
                Hit("OK", "REL/valid_result_rejects",
                    "T is not a result cell; token and bare ? are not matrices");

            try
            {
                var (kind, val) = Oracle.ParseRelateWire("?????????");
                if (kind == "matrix" && val == "?????????")
                    Hit("OK", "REL/matrix_all_unknown",
                        "nine ? is a matrix, not Decline");
                else
                    Hit("FAIL", "REL/matrix_all_unknown", $"got {kind} {val}");
            }
            catch (Exception ex) { Hit("FAIL", "REL/matrix_all_unknown", ex.Message); }
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

        Console.WriteLine("=== RING_SIMPLE vs NTS IsSimple (615-h rungs 1-3: #624, #630, #634) ===");
        // CircularString simplicity is decided on the branch for every
        // segment count (pairwise contact kernel mirroring this lane's
        // composition). Collinear segments are sent to the oracle AS chords
        // ("C ..."), since the lane's arc parser requires a circumcentre and
        // answers DEGENERATE for collinear controls. Semantics note: the
        // lane models a RING (the chain's first/last segments are always
        // adjacent there), so open-chain vectors appear only where that
        // difference cannot bite; closed values map exactly. Fail-closed
        // contract rows: the degenerate closed segment (the oracle itself
        // declines it, DEGENERATE), the flat-arc conditioning guard, and —
        // since the rung-4 review — the tangency refusal band (exact
        // tangencies the exact-rational oracle decides but doubles cannot).
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
                // The fail-closed contract row (the degenerate closed
                // segment, which the oracle itself declines).
                if (nts is null)
                    Hit("OK", $"SIMPLE/{v.Name}", $"oracle={oOut}; nts fail-closed (contract)");
                else
                    Hit("BUG", $"SIMPLE/{v.Name}",
                        $"oracle={oOut}; nts answered {nts} but this row's contract is fail-closed");
            }
        }

        Console.WriteLine("=== HOLES_DISJOINT vs NTS ring-pair validity (615-h rung 4: #639) ===");
        // The lane classifies two RING REGIONS: DISJOINT, boundary meet
        // ("NOT_DISJOINT CROSS iA iB x y"), or nesting (A_IN_B / B_IN_A).
        // The NTS side probes IsValid on a value composed from the same
        // rings. Semantics note: the oracle's NOT_DISJOINT covers ANY
        // boundary meet or nesting, while the NTS rules implemented this
        // rung refute a CurvePolygon ring pair only at >= 2 boundary
        // contacts or a shared 1-D piece (8.2.1 Desc 11), and a
        // MultiSurface element pair only at a shared 1-D piece (4.2.27
        // permits finitely many POINT contacts). Since rung 5 (#641) the
        // containment machinery decides one-contact tangency, nesting and
        // interiors-disjoint, so a single boundary meet (oracle CROSS) can
        // be a VALID polygon (a tangent hole) or MultiSurface (a corner
        // touch). OracleExpected is a verdict PREFIX: CROSS rows carry
        // indices and a hex-float point after it.
        foreach (var v in Cases.HolesDisjoint)
        {
            string stdin = $"HOLES_DISJOINT\n{v.SegsA.Length}\n" + string.Join("\n", v.SegsA)
                + $"\n{v.SegsB.Length}\n" + string.Join("\n", v.SegsB) + "\n";
            string oOut;
            try { oOut = Oracle.Run(stdin); }
            catch (Exception ex) { Hit("FAIL", $"HOLES/{v.Name}", $"oracle: {ex.Message}"); continue; }

            if (!oOut.StartsWith(v.OracleExpected, StringComparison.Ordinal))
            {
                Hit("FAIL", $"HOLES/{v.Name}", $"oracle={oOut} (exp prefix {v.OracleExpected})");
                continue;
            }

            var g = v.Geometry(gf);
            bool? nts;
            try { nts = g.IsValid; }
            catch (NotSupportedException) { nts = null; }

            if (v.NtsExpected is bool expected)
            {
                if (nts == expected)
                    Hit("OK", $"HOLES/{v.Name}", $"oracle={oOut} nts_isvalid={nts}");
                else
                    Hit("BUG", $"HOLES/{v.Name}",
                        $"oracle={oOut} nts_isvalid={(object?)nts ?? "throw"} (exp {expected})");
            }
            else
            {
                // Fail-closed contract rows: the frontier past Desc 11 /
                // the 1-D boundary rule (containment, interiors-disjoint).
                if (nts is null)
                    Hit("OK", $"HOLES/{v.Name}", $"oracle={oOut}; nts fail-closed (contract)");
                else
                    Hit("BUG", $"HOLES/{v.Name}",
                        $"oracle={oOut}; nts answered {nts} but this row's contract is fail-closed");
            }
        }

        Console.WriteLine("=== CP containment / MS interiors vs NTS IsValid rung 5 (615-h / #641) ===");
        // POINT_IN_CURVE_RING (arc-aware ray cast) and HOLES_DISJOINT
        // (boundary meet + nesting) against NTS's exact point-in-ring, as
        // observed through public IsValid: a hole sample IN the shell <-> the
        // hole is contained; nested / overlapping regions <-> invalid. Query
        // points stay in the oracle lane's generic position (no ray through a
        // vertex, no boundary point). The lens row is the #981 frontier:
        // the oracle decides, NTS must throw. (Tangent / far-outside / corner
        // rows live in the HOLES_DISJOINT section above.)
        foreach (var v in Cases.Containment)
        {
            string oOut;
            try { oOut = Oracle.Run(v.Stdin); }
            catch (Exception ex) { Hit("FAIL", $"CONTAIN/{v.Name}", $"oracle: {ex.Message}"); continue; }
            if (!oOut.StartsWith(v.OracleExpected, StringComparison.Ordinal))
            {
                Hit("FAIL", $"CONTAIN/{v.Name}", $"oracle={oOut} (exp {v.OracleExpected})");
                continue;
            }
            bool? nts;
            try { nts = v.Geometry(gf).IsValid; }
            catch (NotSupportedException) { nts = null; }
            if (nts == v.NtsExpected)
                Hit("OK", $"CONTAIN/{v.Name}",
                    $"oracle={oOut} nts={(nts is null ? "fail-closed (contract)" : nts.ToString())}");
            else
                Hit("BUG", $"CONTAIN/{v.Name}",
                    $"oracle={oOut} nts={(object?)nts ?? "throw"} (exp {(object?)v.NtsExpected ?? "throw"})");
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
    /// True iff <paramref name="s"/> is a 9-char result matrix (cells F/0/1/2/?).
    /// A <c>?</c> cell is uncomputed (523-b), not Decline and not a catalog key.
    /// Pattern <c>T</c> is not a result cell.
    /// </summary>
    public static bool IsValidDe9imResult(string s)
    {
        string t = s.Trim();
        return t.Length == 9 && t.All(c => c is 'F' or '0' or '1' or '2' or '?');
    }

    /// <summary>
    /// Classify one RELATE_MATRIX oracle line.
    /// <c>UNSUPPORTED</c> is a decline (result position only), not a parse error.
    /// Two kinds only — no third kind for <c>?</c>.
    /// </summary>
    public static (string Kind, string Value) ParseRelateWire(string s)
    {
        string t = s.Trim();
        if (t == "UNSUPPORTED")
            return ("token", t);
        if (IsValidDe9imResult(t))
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
        // Flipped three times: rung 2 (#630) decided it, the rung-4 review
        // fail-closed it (inside the tangency band a touch cannot be told
        // from a close crossing pair at double precision), and rung 5 (#641)
        // decides the band's exact discriminant: an exact external tangency
        // at the permitted shared vertex — SIMPLE, as the oracle says.
        ("two_arcs_tangent_at_vertex", new[] { "A 0 0 1 1 2 0", "A 2 0 3 -1 4 0" }, "SIMPLE", true,
            gf => Cs(gf, (0, 0), (1, 1), (2, 0), (3, -1), (4, 0))),
        // Transversal replacement pin: both connecting vertices are genuine
        // crossings (discriminants far above the band), so a multi-arc
        // chain still gets a checked verdict.
        ("two_arcs_transversal_at_vertex",
            new[] { "A 0 0 1 1 2 0", "A 2 0 2.7071067811865475 -0.2928932188134525 3 -1" }, "SIMPLE", true,
            gf => Cs(gf, (0, 0), (1, 1), (2, 0), (2.7071067811865475, -0.2928932188134525), (3, -1))),
        // Closed values map exactly onto the lane's ring semantics.
        ("full_circle_idiom_ring", new[] { "A 0 0 1 1 2 0", "A 2 0 1 -1 0 0" }, "SIMPLE", true,
            gf => Cs(gf, (0, 0), (1, 1), (2, 0), (1, -1), (0, 0))),
        ("there_and_back_overlap", new[] { "A 0 0 1 1 2 0", "A 2 0 1 1 0 0" }, "NOT_SIMPLE", false,
            gf => Cs(gf, (0, 0), (1, 1), (2, 0), (1, 1), (0, 0))),
        // Open 3-segment chain whose last chord touches the first arc at
        // (1,1): not permitted under either semantics (the ring model's
        // closing-pair allowance is (0,0), not (1,1)).
        ("non_adjacent_touch", new[] { "A 0 0 1 1 2 0", "A 2 0 3 -1 4 0", "C 4 0 1 1" }, "NOT_SIMPLE", false,
            gf => Cs(gf, (0, 0), (1, 1), (2, 0), (3, -1), (4, 0), (2.5, 0.5), (1, 1))),
        // CompoundCurve chains (615-h rung 3, #634): the same lane serves
        // mixed arc/chord chains; LineString components map to "C" segments.
        ("cc_semicircle_diameter_ring", new[] { "A 0 0 1 1 2 0", "C 2 0 0 0" }, "SIMPLE", true,
            gf => new CompoundCurve(new Curve[]
            {
                Cs(gf, (0, 0), (1, 1), (2, 0)),
                gf.CreateLineString(new[] { new Coordinate(2, 0), new Coordinate(0, 0) }),
            }, gf)),
        // Both refuting contacts here are exact LINE tangencies (x = 2 at
        // (2,0), y = 1 at (1,1)). Fail-closed after the rung-4 review;
        // rung 5 (#641) decides them exactly (rational foot of the
        // perpendicular): the y = 1 touch at (1,1) refutes — NOT_SIMPLE.
        ("cc_line_tangent_arc", new[] { "A 0 0 1 1 2 0", "C 2 0 2 1", "C 2 1 0 1" }, "NOT_SIMPLE", false,
            gf => new CompoundCurve(new Curve[]
            {
                Cs(gf, (0, 0), (1, 1), (2, 0)),
                gf.CreateLineString(new[]
                {
                    new Coordinate(2, 0), new Coordinate(2, 1), new Coordinate(0, 1),
                }),
            }, gf)),
        // The exact/double split (615-h rung-2 review): the flat arc's
        // circumradius (~2e8) is beyond double precision for contact
        // decisions, so NTS refuses (conditioning guard) while the
        // exact-rational oracle decides — it even finds the genuine second
        // crossing of the flat arc and its connector chord 2.8e-8 from the
        // shared vertex.
        ("flat_arc_ill_conditioned", new[] { "A -2 0.9 0 0.90000001 2 0.9", "C 2 0.9 1 0", "A 1 0 0 1 -1 0" }, "NOT_SIMPLE", null,
            gf => Cs(gf, (-2, 0.9), (0, 0.90000001), (2, 0.9), (1.5, 0.45), (1, 0), (0, 1), (-1, 0))),
        ("bowtie_4chords", new[] { "C 0 0 2 2", "C 2 2 2 0", "C 2 0 0 2", "C 0 2 0 0" }, "NOT_SIMPLE", false,
            gf => gf.CreateLineString(new[]
            {
                new Coordinate(0, 0), new Coordinate(2, 2), new Coordinate(2, 0),
                new Coordinate(0, 2), new Coordinate(0, 0),
            })),
    };

    /// <summary>
    /// HOLES_DISJOINT vectors (Proofs #615 ticket 615-h, #639 rung 4). SegsA
    /// and SegsB are the two rings on the oracle wire; Geometry composes the
    /// same rings into the NTS value whose IsValid is probed (a CurvePolygon
    /// shell+hole, or a two-element MultiSurface). NtsExpected: a bool for a
    /// decided verdict, null for the fail-closed contract (none since rung 5,
    /// #641; the remaining frontier rows live in Cases.Containment).
    /// </summary>
    public static readonly (string Name, string[] SegsA, string[] SegsB, string OracleExpected, bool? NtsExpected, Func<GeometryFactory, Geometry> Geometry)[] HolesDisjoint =
    {
        // Two proper crossings between shell and hole: >= 2 contacts, so
        // 8.2.1 Desc 11 gives definite false.
        ("cp_hole_crosses_shell",
            new[] { "A 0 0 2 2 4 0", "A 4 0 2 -2 0 0" },
            new[] { "A 3 1 5 3 7 1", "A 7 1 5 -1 3 1" },
            "NOT_DISJOINT CROSS", false,
            gf => new CurvePolygon(Cs(gf, (0, 0), (2, 2), (4, 0), (2, -2), (0, 0)),
                new Curve[] { Cs(gf, (3, 1), (5, 3), (7, 1), (5, -1), (3, 1)) }, gf)),
        // Internal tangency at (4,0) — #641's canonical witness. The oracle
        // reports the boundary meet; rung 5 decides the touch exactly (one
        // contact passes Desc 11), the hole is inside the shell and the
        // touch graph is a tree: a VALID polygon.
        ("cp_hole_tangent_internal",
            new[] { "A 0 0 2 2 4 0", "A 4 0 2 -2 0 0" },
            new[] { "A 2 0 3 1 4 0", "A 4 0 3 -1 2 0" },
            "NOT_DISJOINT CROSS", true,
            gf => new CurvePolygon(Cs(gf, (0, 0), (2, 2), (4, 0), (2, -2), (0, 0)),
                new Curve[] { Cs(gf, (2, 0), (3, 1), (4, 0), (3, -1), (2, 0)) }, gf)),
        // Hole region fully outside the shell (oracle: DISJOINT regions):
        // since rung 5 the exact containment check refutes it (8.2.1
        // Desc 12) — definite false.
        ("cp_hole_far_outside",
            new[] { "A 0 0 2 2 4 0", "A 4 0 2 -2 0 0" },
            new[] { "A 10 0 12 2 14 0", "A 14 0 12 -2 10 0" },
            "DISJOINT", false,
            gf => new CurvePolygon(Cs(gf, (0, 0), (2, 2), (4, 0), (2, -2), (0, 0)),
                new Curve[] { Cs(gf, (10, 0), (12, 2), (14, 0), (12, -2), (10, 0)) }, gf)),
        // Proper nesting with no boundary contact (the legal hole shape):
        // the oracle certifies B_IN_A and rung 5 confirms containment —
        // VALID. (The hole's two arcs have non-dyadic intermediates, so their
        // exact circles differ; both pass through the shared vertices, which
        // anchor the exact crossing-pair placement.) The inner ring sits
        // off-axis so the lane's nesting ray cast does not pass through an
        // outer-ring vertex.
        ("cp_hole_nested_offaxis",
            new[] { "A 0 0 2 2 4 0", "A 4 0 2 -2 0 0" },
            new[] { "A 1 0.2 2 1.2 3 0.2", "A 3 0.2 2 -0.8 1 0.2" },
            "NOT_DISJOINT B_IN_A", true,
            gf => new CurvePolygon(Cs(gf, (0, 0), (2, 2), (4, 0), (2, -2), (0, 0)),
                new Curve[] { Cs(gf, (1, 0.2), (2, 1.2), (3, 0.2), (2, -0.8), (1, 0.2)) }, gf)),
        // Two surface elements whose boundaries share the whole upper
        // semicircle (a 1-D piece): 4.2.27 definite false on the
        // MultiSurface (the exactly-cocircular kernel path).
        ("ms_shared_arc",
            new[] { "A 0 0 1 1 2 0", "A 2 0 1 -1 0 0" },
            new[] { "A 0 0 1 1 2 0", "C 2 0 0 0" },
            "NOT_DISJOINT CROSS", false,
            gf => new MultiSurface(new Geometry[]
            {
                new CurvePolygon(Cs(gf, (0, 0), (1, 1), (2, 0), (1, -1), (0, 0)), gf),
                new CurvePolygon(new CompoundCurve(new Curve[]
                {
                    Cs(gf, (0, 0), (1, 1), (2, 0)),
                    gf.CreateLineString(new[] { new Coordinate(2, 0), new Coordinate(0, 0) }),
                }, gf), gf),
            }, gf)),
        // Classical squares sharing a full edge: the same 1-D rule through
        // the chord-chord path.
        ("ms_shared_edge_squares",
            new[] { "C 0 0 4 0", "C 4 0 4 4", "C 4 4 0 4", "C 0 4 0 0" },
            new[] { "C 4 0 8 0", "C 8 0 8 4", "C 8 4 4 4", "C 4 4 4 0" },
            "NOT_DISJOINT CROSS", false,
            gf => new MultiSurface(new Geometry[] { Sq(gf, 0, 0, 4), Sq(gf, 4, 0, 4) }, gf)),
        // Corner touch: a POINT contact is permitted boundary contact under
        // 4.2.27, and since rung 5 the all-classical MultiSurface takes the
        // classical MultiPolygon rule (which IS 4.2.27): VALID.
        ("ms_corner_touch_squares",
            new[] { "C 0 0 4 0", "C 4 0 4 4", "C 4 4 0 4", "C 0 4 0 0" },
            new[] { "C 4 4 8 4", "C 8 4 8 8", "C 8 8 4 8", "C 4 8 4 4" },
            "NOT_DISJOINT CROSS", true,
            gf => new MultiSurface(new Geometry[] { Sq(gf, 0, 0, 4), Sq(gf, 4, 4, 4) }, gf)),
    };

    /// <summary>
    /// Containment vectors (Proofs #615 ticket 615-h, #641 rung 5). Stdin is
    /// the full oracle input; OracleExpected a prefix of its verdict;
    /// NtsExpected the IsValid verdict of the geometry built from the same
    /// rings (null: the fail-closed contract — NTS must throw).
    /// </summary>
    public static readonly (string Name, string Stdin, string OracleExpected, bool? NtsExpected, Func<GeometryFactory, Geometry> Geometry)[] Containment =
        BuildContainment();

    private static (string, string, string, bool?, Func<GeometryFactory, Geometry>)[] BuildContainment()
    {
        static string Ring(params string[] segs) => $"{segs.Length}\n" + string.Join("\n", segs) + "\n";
        static string Pir(string ring, string query) => "POINT_IN_CURVE_RING\n" + ring + query + "\n";
        static string Hd(string a, string b) => "HOLES_DISJOINT\n" + a + b;
        // Circles as the two-segment five-point idiom (WKT order).
        static CircularString Circle(GeometryFactory gf, double cx, double cy, double r) =>
            Cs(gf, (cx - r, cy), (cx, cy + r), (cx + r, cy), (cx, cy - r), (cx - r, cy));
        static string CircleRing(double cx, double cy, double r)
        {
            string F(double d) => d.ToString("R", CultureInfo.InvariantCulture);
            return Ring($"A {F(cx - r)} {F(cy)} {F(cx)} {F(cy + r)} {F(cx + r)} {F(cy)}",
                        $"A {F(cx + r)} {F(cy)} {F(cx)} {F(cy - r)} {F(cx - r)} {F(cy)}");
        }
        static CurvePolygon Cp(GeometryFactory gf, Curve shell, params Curve[] holes) => new CurvePolygon(shell, holes, gf);

        const double hx = 0.7865526304750483, hy = 1.213447369524952;
        return new (string, string, string, bool?, Func<GeometryFactory, Geometry>)[]
        {
            ("cp_concentric_hole", Pir(CircleRing(2, 0, 2), "2 1"), "IN", true,
                gf => Cp(gf, Circle(gf, 2, 0, 2), Circle(gf, 2, 0, 1))),
            ("cp_externally_tangent_hole", Pir(CircleRing(2, 0, 2), "5 1"), "OUT", false,
                gf => Cp(gf, Circle(gf, 2, 0, 2), Circle(gf, 5, 0, 1))),
            // Rung-4 review witness W2 (exactly tangent at (2,0)).
            ("cp_w2_tangent_compound_hole",
                Pir(Ring("A 0 2 2 0 0 -2", "A 0 -2 -2 0 0 2"),
                    $"{hx.ToString("R", CultureInfo.InvariantCulture)} {hy.ToString("R", CultureInfo.InvariantCulture)}"),
                "IN", true,
                gf => Cp(gf, Cs(gf, (0, 2), (2, 0), (0, -2), (-2, 0), (0, 2)),
                    new CompoundCurve(new Curve[]
                    {
                        Cs(gf, (hx, hy), (2, 0), (hx, -hy)),
                        gf.CreateLineString(new[]
                        {
                            new Coordinate(hx, -hy), new Coordinate(hx - 0.3, 0), new Coordinate(hx, hy),
                        }),
                    }, gf))),
            // The inner ring starts at its top vertex: the lane tests nesting
            // from ring B's first vertex, and from (-1,0) the ray would pass
            // through ring A's shared arc endpoint (2,0) (not generic).
            ("cp_nested_holes", Hd(CircleRing(0, 0, 2), Ring("A 0 1 1 0 0 -1", "A 0 -1 -1 0 0 1")),
                "NOT_DISJOINT B_IN_A", false,
                gf => Cp(gf, Circle(gf, 0, 0, 4), Circle(gf, 0, 0, 2),
                    Cs(gf, (0, 1), (1, 0), (0, -1), (-1, 0), (0, 1)))),
            ("cp_two_separate_holes", Hd(CircleRing(-2, 0, 1), CircleRing(2, 0, 1)), "DISJOINT", true,
                gf => Cp(gf, Circle(gf, 0, 0, 4), Circle(gf, -2, 0, 1), Circle(gf, 2, 0, 1))),
            ("ms_disjoint_circles", Hd(CircleRing(1, 0, 1), CircleRing(6, 0, 1)), "DISJOINT", true,
                gf => new MultiSurface(new Geometry[]
                    { Cp(gf, Circle(gf, 1, 0, 1)), Cp(gf, Circle(gf, 6, 0, 1)) }, gf)),
            ("ms_island_in_annulus_hole", Pir(CircleRing(0, 0, 2), "0 1"), "IN", true,
                gf => new MultiSurface(new Geometry[]
                {
                    Cp(gf, Circle(gf, 0, 0, 4), Circle(gf, 0, 0, 2)),
                    Cp(gf, Circle(gf, 0, 0, 1)),
                }, gf)),
            ("ms_overlapping_circles", Hd(CircleRing(0, 0, 2), CircleRing(3, 0, 2)), "NOT_DISJOINT", false,
                gf => new MultiSurface(new Geometry[]
                    { Cp(gf, Circle(gf, 0, 0, 2)), Cp(gf, Circle(gf, 3, 0, 2)) }, gf)),
            // The #981 frontier: a thin lens with no control point inside the
            // other circle and crossings away from any vertex.
            ("ms_lens_frontier",
                Hd(Ring("A 5 0 0 5 -5 0", "A -5 0 0 -5 5 0"), Ring("A 12 7 7 12 2 7", "A 2 7 7 2 12 7")),
                "NOT_DISJOINT", null,
                gf => new MultiSurface(new Geometry[]
                {
                    Cp(gf, Cs(gf, (5, 0), (0, 5), (-5, 0), (0, -5), (5, 0))),
                    Cp(gf, Cs(gf, (12, 7), (7, 12), (2, 7), (7, 2), (12, 7))),
                }, gf)),
        };
    }

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

    private static Polygon Sq(GeometryFactory gf, double x, double y, double s) =>
        gf.CreatePolygon(new[]
        {
            new Coordinate(x, y), new Coordinate(x + s, y),
            new Coordinate(x + s, y + s), new Coordinate(x, y + s),
            new Coordinate(x, y),
        });

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
        ("TOUCH_SAME", "triangle_pair_fill TPR_SameCone", "token", "UNSUPPORTED",
            "Leftover Ⅵ same-sign spill. Inhabits; fill not named."),
        ("LENS", "triangle_pair_fill TPR_Lens", "token", "UNSUPPORTED",
            "Leftover Ⅶ edge-cross residue. Inhabits; fill not named."),
        ("INSIDE", "triangle_pair_fill TPR_Inside", "token", "UNSUPPORTED",
            "Leftover Ⅷ nested containment. Inhabits; fill not named."),
        ("NEST", "triangle_pair_fill TPR_Nest", "token", "UNSUPPORTED",
            "Leftover Ⅸ same-side shared-edge nest. Inhabits; fill not named."),
        ("DECLINE", "triangle_pair_fill TPR_Unsupported", "token", "UNSUPPORTED",
            "Unnamed swap nest. Leftover Ⅸ names the nest."),
    };
}
