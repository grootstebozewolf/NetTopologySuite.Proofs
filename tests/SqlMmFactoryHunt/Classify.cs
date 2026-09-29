// Verdicts: OK / INTERESTING / DIVERGE / BUG — factory emit vs intake μ + WKB contract.
// Assisted-by: Cursor Grok 4.6. claimId: none (tools).

using System.Buffers.Binary;
using System.Text.RegularExpressions;

sealed class Counts
{
    public int Ok, Interesting, Diverge, Bug;

    public void Add(string kind)
    {
        switch (kind)
        {
            case "OK": Ok++; break;
            case "INTERESTING": Interesting++; break;
            case "DIVERGE": Diverge++; break;
            case "BUG": Bug++; break;
        }
    }
}

sealed class WkbDec
{
    public bool Hold;
    public string HoldText = "";
    public int Order = -1;
    public int Typ = -1;
    public int Nbytes;
    public int Npts;
    public List<Xy> Coords = [];
    public List<WkbDec> Children = [];
    public string Err = "";
}

static class Classify
{
    internal static void Emit(string kind, string trial, string wkt, string reason, Counts counts)
    {
        counts.Add(kind);
        Console.WriteLine($"{kind} {trial} WKT={Snippet(wkt)} {reason}");
    }

    internal static string Snippet(string wkt, int n = 72)
    {
        string w = string.Join(' ', wkt.Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries));
        return w.Length <= n ? w : w[..(n - 3)] + "...";
    }

    internal static void Trial(
        string trial,
        string wkt,
        string factoryBag,
        string factoryTau,
        string intakeWire,
        Dictionary<string, string> fields,
        Model? m,
        Counts counts,
        string extra = "",
        bool factoryEmitted = true)
    {
        var reasons = new List<string>();
        string kind = "OK";

        if (factoryEmitted && m is { Keyword: "LINESTRING" }
            && wkt.StartsWith("GEODESICSTRING", StringComparison.OrdinalIgnoreCase))
        {
            kind = "BUG";
            reasons.Add("factory emitted GEODESICSTRING (must be LINESTRING / τ=TagLineString)");
        }
        if (factoryTau == "TagGeodesic")
        {
            kind = "BUG";
            reasons.Add("τ=TagGeodesic (unhold geodesic)");
        }

        string expKind = m?.ExpectKind ?? "BAG";
        string? expDec = m?.ExpectDecline;
        Bag? expBag = m?.ExpectBag;

        var (iKind, iBag, iDec) = Wire.Parse(intakeWire);
        var (fKind, fBag, _) = Wire.Parse(factoryBag);

        if (iKind == "OTHER")
        {
            kind = "BUG";
            reasons.Add($"intake-not-wire:{intakeWire[..Math.Min(60, intakeWire.Length)]}");
        }
        else if (expKind == "BAG")
        {
            if (iKind == "DECLINE")
            {
                if (iDec == "ID_ParseFail")
                {
                    kind = "BUG";
                    reasons.Add("intake ID_ParseFail on factory WKT");
                }
                else
                {
                    kind = "DIVERGE";
                    reasons.Add($"expected BAG got {intakeWire}");
                }
            }
            else if (expBag != null && iBag != null && !Wire.BagsEqual(expBag, iBag))
            {
                kind = "DIVERGE";
                reasons.Add($"μ≠expect expect={expBag.ToWire()} got={intakeWire}");
            }
        }
        else if (expKind == "DECLINE")
        {
            if (iKind != "DECLINE")
            {
                kind = "DIVERGE";
                reasons.Add($"expected {expDec} got {intakeWire}");
            }
            else if (expDec != null && iDec != expDec)
            {
                kind = "DIVERGE";
                reasons.Add($"expected {expDec} got {iDec}");
            }
        }

        if (iKind == "BAG" && fKind == "BAG" && iBag != null && fBag != null)
        {
            if (!Wire.BagsEqual(fBag, iBag))
            {
                if (kind == "OK") kind = "DIVERGE";
                reasons.Add($"factory_bag≠μ factory={factoryBag} μ={intakeWire}");
            }
        }
        else if (expKind == "DECLINE" && fKind == "BAG" && iKind == "DECLINE")
        {
            if (kind == "OK") kind = "INTERESTING";
            reasons.Add($"factory rendered Decline-bound WKT factory_bag={factoryBag} intake={intakeWire}");
        }

        foreach (var (sev, note) in CheckWkb(fields, m))
        {
            if (sev == "BUG") kind = "BUG";
            else if (sev == "DIVERGE" && kind is "OK" or "INTERESTING") kind = "DIVERGE";
            reasons.Add(note);
        }

        if (extra.Length > 0)
            reasons.Add(extra);
        if (reasons.Count == 0)
            reasons.Add("bag+wkb+grammar match");
        Emit(kind, trial, wkt, string.Join("; ", reasons), counts);
    }

    internal static void RunModel(Model m, Counts counts, string tag)
    {
        var (rc, stdout, err) = HuntHost.FactoryStdin(m.Text());
        if (rc != 0)
        {
            Emit("BUG", tag, m.Keyword, $"factory-stdin rc={rc} {TrimErr(err)}", counts);
            return;
        }
        var fields = HuntHost.ParseFields(stdout);
        string wkt = fields.GetValueOrDefault("WKT", "");
        var (irc, iout, _) = HuntHost.Intake(wkt);
        _ = irc;
        Trial(tag, wkt, fields.GetValueOrDefault("BAG", ""), fields.GetValueOrDefault("TAU", ""),
            iout.Trim(), fields, m, counts);
    }

    internal static void RunCatalogPin(string exampleId, Counts counts)
    {
        var (rc, stdout, err) = HuntHost.FactoryId(exampleId);
        if (rc != 0)
        {
            Emit("BUG", $"pin:catalog:{exampleId}", "", $"factory rc={rc} {TrimErr(err)}", counts);
            return;
        }
        var fields = HuntHost.ParseFields(stdout);
        string wkt = fields.GetValueOrDefault("WKT", "");
        var m = Wire.CatalogExpect(exampleId, fields);
        bool strict = exampleId.EndsWith("-strict", StringComparison.Ordinal);
        var (_, iout, _) = HuntHost.Intake(wkt, strict);
        Trial($"pin:catalog:{exampleId}", wkt, fields.GetValueOrDefault("BAG", ""),
            fields.GetValueOrDefault("TAU", ""), iout.Trim(), fields, m, counts);
    }

    internal static void RunIntakeOnly(string tag, string wkt, Model expect, Counts counts)
    {
        var (_, iout, _) = HuntHost.Intake(wkt);
        var holdFields = new Dictionary<string, string>
        {
            ["WKB-NDR"] = "HOLD intake-only",
            ["WKB-XDR"] = "HOLD intake-only",
        };
        string factoryBag = expect.ExpectBag?.ToWire() ?? $"DECLINE {expect.ExpectDecline}";
        Trial(tag, wkt, factoryBag, expect.Tau, iout.Trim(), holdFields,
            new Model
            {
                Mid = expect.Mid,
                Keyword = expect.Keyword,
                ExpectKind = expect.ExpectKind,
                ExpectDecline = expect.ExpectDecline,
                ExpectBag = expect.ExpectBag,
                Hold = true,
                Tau = expect.Tau,
            },
            counts,
            extra: "intake-only (no factory emit)",
            factoryEmitted: false);
    }

    static string TrimErr(string err)
    {
        err = err.Trim().Replace('\n', ' ');
        return err.Length <= 100 ? err : err[..100];
    }

    static List<(string Sev, string Note)> CheckWkb(Dictionary<string, string> fields, Model? m)
    {
        var notes = new List<(string, string)>();
        string ndr = fields.GetValueOrDefault("WKB-NDR", "");
        string xdr = fields.GetValueOrDefault("WKB-XDR", "");
        bool holdExpected = m?.Hold == true;
        int? signed = m?.SignedWkb;

        foreach (var (label, h) in new[] { ("NDR", ndr), ("XDR", xdr) })
        {
            if (string.IsNullOrEmpty(h))
            {
                notes.Add(("BUG", $"missing WKB-{label}"));
                continue;
            }
            int? bad = LooksLikeForbiddenSigned(h);
            if (bad is int t)
                notes.Add(("BUG", $"WKB-{label} signed type {t} (13/18/22 forbidden)"));
            if (holdExpected)
            {
                if (!h.StartsWith("HOLD", StringComparison.OrdinalIgnoreCase))
                    notes.Add(("BUG", $"HOLD type leaked hex WKB-{label}={Head(h, 24)}"));
                else if (Regex.IsMatch(h, @"(^|[^0-9])(13|18|22)([^0-9]|$)")
                         && Regex.IsMatch(h.Trim(), @"^[0-9A-Fa-f]+$"))
                    notes.Add(("BUG", $"HOLD hex looks like type code: {Head(h, 24)}"));
            }
            else if (signed is int s && Wire.SignedTypes.Contains(s))
            {
                if (h.StartsWith("HOLD", StringComparison.OrdinalIgnoreCase))
                    notes.Add(("DIVERGE", $"signed type {s} emitted HOLD {Head(h, 40)}"));
                else
                {
                    var dec = DecodeWkb(h);
                    int wantOrder = label == "NDR" ? 1 : 0;
                    if (dec.Hold) notes.Add(("BUG", $"signed decode HOLD {label}"));
                    else if (dec.Err.Length > 0) notes.Add(("DIVERGE", $"WKB-{label} {dec.Err}"));
                    else if (dec.Typ != s) notes.Add(("BUG", $"WKB-{label} type={dec.Typ} want={s}"));
                    else if (dec.Order != wantOrder) notes.Add(("DIVERGE", $"WKB-{label} order={dec.Order} want={wantOrder}"));
                }
            }
        }

        if (signed is int sg && Wire.SignedTypes.Contains(sg)
            && ndr.Length > 0 && xdr.Length > 0
            && !ndr.StartsWith("HOLD", StringComparison.OrdinalIgnoreCase))
        {
            var a = DecodeWkb(ndr);
            var b = DecodeWkb(xdr);
            if (string.Equals(ndr, xdr, StringComparison.OrdinalIgnoreCase))
                notes.Add(("DIVERGE", "NDR hex equals XDR (endianness must differ)"));
            if (a.Nbytes != 0 && b.Nbytes != 0 && a.Nbytes != b.Nbytes)
                notes.Add(("DIVERGE", $"WKB length NDR={a.Nbytes} XDR={b.Nbytes}"));
            if (!a.Hold && !b.Hold && !LogicalWkbEqual(a, b))
                notes.Add(("DIVERGE", "NDR/XDR logical payload differ (not just endianness)"));
            if (m is { Controls.Count: > 0 } && sg is 2 or 8 && a.Err.Length == 0 && !m.Empty
                && a.Npts != m.Controls.Count)
                notes.Add(("DIVERGE", $"WKB npts={a.Npts} controls={m.Controls.Count}"));
        }
        return notes;
    }

    static string Head(string h, int n) => h.Length <= n ? h : h[..n];

    static int? LooksLikeForbiddenSigned(string h)
    {
        string t = h.Trim();
        if (t.StartsWith("HOLD", StringComparison.OrdinalIgnoreCase))
            return null;
        byte[] raw;
        try { raw = Convert.FromHexString(t); }
        catch { return null; }
        if (raw.Length < 5) return null;
        int order = raw[0];
        if (order is not (0 or 1)) return null;
        int typ = order == 1
            ? BinaryPrimitives.ReadInt32LittleEndian(raw.AsSpan(1, 4))
            : BinaryPrimitives.ReadInt32BigEndian(raw.AsSpan(1, 4));
        return Wire.ForbiddenSigned.Contains(typ) ? typ : null;
    }

    internal static WkbDec DecodeWkb(string h)
    {
        string t = h.Trim();
        if (t.StartsWith("HOLD", StringComparison.OrdinalIgnoreCase))
            return new WkbDec { Hold = true, HoldText = t };
        byte[] raw;
        try { raw = Convert.FromHexString(t); }
        catch { return new WkbDec { Err = $"not-hex:{Head(t, 40)}" }; }
        if (raw.Length < 5)
            return new WkbDec { Err = $"short:{raw.Length}", Nbytes = raw.Length };
        int order = raw[0];
        bool ndr = order == 1;
        if (order is not (0 or 1))
            return new WkbDec { Err = $"bad-order:{order:x2}", Nbytes = raw.Length };
        int typ = ndr
            ? BinaryPrimitives.ReadInt32LittleEndian(raw.AsSpan(1, 4))
            : BinaryPrimitives.ReadInt32BigEndian(raw.AsSpan(1, 4));
        var dec = new WkbDec { Order = order, Typ = typ, Nbytes = raw.Length };
        try
        {
            int pos = 5;
            if (typ == 1)
            {
                if (raw.Length != 21) dec.Err = $"point-len:{raw.Length}";
                dec.Coords.Add(ReadXy(raw, pos, ndr));
                dec.Npts = 1;
            }
            else if (typ is 2 or 8)
            {
                int n = ndr
                    ? BinaryPrimitives.ReadInt32LittleEndian(raw.AsSpan(pos, 4))
                    : BinaryPrimitives.ReadInt32BigEndian(raw.AsSpan(pos, 4));
                pos += 4;
                dec.Npts = n;
                int want = 9 + 16 * n;
                if (raw.Length != want) dec.Err = $"counted-len:{raw.Length} want={want}";
                for (int i = 0; i < n; i++)
                {
                    dec.Coords.Add(ReadXy(raw, pos, ndr));
                    pos += 16;
                }
            }
            else if (typ == 9)
            {
                int n = ndr
                    ? BinaryPrimitives.ReadInt32LittleEndian(raw.AsSpan(pos, 4))
                    : BinaryPrimitives.ReadInt32BigEndian(raw.AsSpan(pos, 4));
                pos += 4;
                dec.Npts = n;
                for (int i = 0; i < n; i++)
                {
                    var (childHex, consumed) = SliceChild(raw.AsSpan(pos), ndr);
                    dec.Children.Add(DecodeWkb(childHex));
                    pos += consumed;
                }
                if (pos != raw.Length)
                    dec.Err = $"compound-trailing:{raw.Length - pos}";
            }
            else
                dec.Err = $"unsigned-or-unknown-type:{typ}";
        }
        catch (Exception ex)
        {
            dec.Err = $"decode:{ex.Message}";
        }
        return dec;
    }

    static Xy ReadXy(byte[] raw, int pos, bool ndr)
    {
        double x = ndr
            ? BitConverter.Int64BitsToDouble(BinaryPrimitives.ReadInt64LittleEndian(raw.AsSpan(pos, 8)))
            : BitConverter.Int64BitsToDouble(BinaryPrimitives.ReadInt64BigEndian(raw.AsSpan(pos, 8)));
        double y = ndr
            ? BitConverter.Int64BitsToDouble(BinaryPrimitives.ReadInt64LittleEndian(raw.AsSpan(pos + 8, 8)))
            : BitConverter.Int64BitsToDouble(BinaryPrimitives.ReadInt64BigEndian(raw.AsSpan(pos + 8, 8)));
        return new Xy(x, y);
    }

    static (string Hex, int N) SliceChild(ReadOnlySpan<byte> raw, bool ndrHint)
    {
        _ = ndrHint;
        if (raw.Length < 5)
            return (Convert.ToHexString(raw).ToLowerInvariant(), raw.Length);
        int order = raw[0];
        bool ndr = order == 1;
        int typ = ndr
            ? BinaryPrimitives.ReadInt32LittleEndian(raw[1..5])
            : BinaryPrimitives.ReadInt32BigEndian(raw[1..5]);
        int n;
        if (typ == 1) n = 21;
        else if (typ is 2 or 8)
        {
            int cnt = ndr
                ? BinaryPrimitives.ReadInt32LittleEndian(raw[5..9])
                : BinaryPrimitives.ReadInt32BigEndian(raw[5..9]);
            n = 9 + 16 * cnt;
        }
        else if (typ == 9)
        {
            int pos = 9;
            int nch = ndr
                ? BinaryPrimitives.ReadInt32LittleEndian(raw[5..9])
                : BinaryPrimitives.ReadInt32BigEndian(raw[5..9]);
            for (int i = 0; i < nch; i++)
            {
                var (_, c) = SliceChild(raw[pos..], ndr);
                pos += c;
            }
            n = pos;
        }
        else n = raw.Length;
        return (Convert.ToHexString(raw[..n]).ToLowerInvariant(), n);
    }

    static bool LogicalWkbEqual(WkbDec a, WkbDec b)
    {
        if (a.Hold || b.Hold)
            return a.Hold && b.Hold && a.HoldText == b.HoldText;
        if (a.Typ != b.Typ || a.Err.Length > 0 || b.Err.Length > 0)
            return false;
        if (a.Npts != b.Npts || a.Coords.Count != b.Coords.Count)
            return false;
        for (int i = 0; i < a.Coords.Count; i++)
        {
            if (a.Coords[i].X != b.Coords[i].X || a.Coords[i].Y != b.Coords[i].Y)
                return false;
        }
        if (a.Children.Count != b.Children.Count)
            return false;
        return a.Children.Zip(b.Children).All(p => LogicalWkbEqual(p.First, p.Second));
    }
}
