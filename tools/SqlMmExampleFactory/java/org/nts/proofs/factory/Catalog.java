package org.nts.proofs.factory;

import java.util.LinkedHashMap;
import java.util.Map;
import org.nts.proofs.factory.Example.Pt;

/**
 * Locked Shelf A starters. Bags match {@code tools/WktIntakeWalker/smoke.sh}.
 * GEODESICSTRING is catalogued only as an honest MkChord / TagLineString
 * emit (LINESTRING text, WKB 2) — not TagGeodesic / WKB 13.
 *
 * claimId: none (tools).
 */
public final class Catalog {
    private Catalog() {}

    public static Map<String, Example> all() {
        Map<String, Example> m = new LinkedHashMap<>();
        add(m, point00());
        add(m, pointEmpty());
        add(m, linestring02());
        add(m, linestringEmpty());
        add(m, circularstringQuarter());
        add(m, circularstringFull());
        add(m, circularstringFullStrict());
        add(m, circleFull());
        add(m, compoundLsCs());
        add(m, clothoidJts());
        add(m, clothoidIso());
        add(m, geodesicAsLineString());
        return m;
    }

    public static Example get(String id) {
        Example g = all().get(id);
        if (g == null) {
            throw new IllegalArgumentException("unknown example id: " + id);
        }
        return g;
    }

    private static void add(Map<String, Example> m, Example g) {
        m.put(g.id, g);
    }

    static Example point00() {
        return Example.builder("point-00", "POINT")
                .hens(0)
                .pt(0, 0)
                .control(0, 0)
                .tau("TagLineString")
                .build();
    }

    static Example pointEmpty() {
        return Example.builder("point-empty", "POINT").empty().build();
    }

    static Example linestring02() {
        return Example.builder("linestring-02", "LINESTRING")
                .hens(0, 1)
                .pt(0, 0)
                .pt(2, 0)
                .control(0, 0)
                .control(2, 0)
                .chicken(0, 1, "MkChord")
                .tau("TagLineString")
                .build();
    }

    static Example linestringEmpty() {
        return Example.builder("linestring-empty", "LINESTRING").empty().build();
    }

    static Example circularstringQuarter() {
        return Example.builder("circularstring-quarter", "CIRCULARSTRING")
                .hens(0, 1)
                .pt(5, 0)
                .pt(0, 5)
                .control(5, 0)
                .control(3, 4)
                .control(0, 5)
                .chicken(0, 1, "MkCirc:quarter")
                .tau("TagCircularString")
                .build();
    }

    /** ADR-0005 lenient: CIRCULARSTRING(A,B,A) bags the CCW ISO circle. */
    static Example circularstringFull() {
        return Example.builder("circularstring-full", "CIRCULARSTRING")
                .hens(0, 1)
                .pt(5, 0)
                .pt(0, 5)
                .control(5, 0)
                .control(0, 5)
                .control(5, 0)
                .chicken(0, 1, "MkCirc:half")
                .chicken(1, 0, "MkCirc:half")
                .tau("TagCircularString")
                .build();
    }

    /** ADR-0005 strict: the same text Declines. */
    static Example circularstringFullStrict() {
        return Example.builder("circularstring-full-strict", "CIRCULARSTRING")
                .control(5, 0)
                .control(0, 5)
                .control(5, 0)
                .decline("ID_CsClosedDegenerate")
                .tau("TagCircularString")
                .build();
    }

    static Example circleFull() {
        return Example.builder("circle-full", "CIRCLE")
                .hens(0, 1)
                .pt(5, 0)
                .pt(-5, 0)
                .control(5, 0)
                .control(0, 5)
                .control(-5, 0)
                .chicken(0, 1, "MkCirc:half")
                .chicken(1, 0, "MkCirc:half")
                .tau("TagCircle")
                .build();
    }

    static Example compoundLsCs() {
        Example ls = Example.builder("compound-ls", "LINESTRING")
                .hens(0, 1)
                .pt(0, 0)
                .pt(5, 0)
                .control(0, 0)
                .control(5, 0)
                .chicken(0, 1, "MkChord")
                .tau("TagLineString")
                .build();
        Example cs = Example.builder("compound-cs", "CIRCULARSTRING")
                .hens(0, 1)
                .pt(5, 0)
                .pt(0, 5)
                .control(5, 0)
                .control(3, 4)
                .control(0, 5)
                .chicken(0, 1, "MkCirc:quarter")
                .tau("TagCircularString")
                .build();
        return Example.builder("compound-ls-cs", "COMPOUNDCURVE")
                .hens(0, 1, 2, 3)
                .pt(0, 0)
                .pt(5, 0)
                .pt(5, 0)
                .pt(0, 5)
                .chicken(0, 1, "MkChord")
                .chicken(2, 3, "MkCirc:quarter")
                .child(ls)
                .child(cs)
                .tau("TagLineString")
                .build();
    }

    /** Locked JTS (k0,k1,L) form used by intake smoke. */
    static Example clothoidJts() {
        double y1 = (0.005 - 0.0) * (80.0 * 80.0) / 6.0;
        return Example.builder("clothoid-jts", "CLOTHOID")
                .hens(0, 1)
                .pt(0, 0)
                .pt(80, y1)
                .chicken(0, 1, "MkClothoid")
                .jts("0", "0.005", "80")
                .tau("TagClothoid")
                .build();
    }

    /** ISO REFERENCELOCATION form; same MkClothoid bag as JTS. */
    static Example clothoidIso() {
        double y1 = (0.005 - 0.0) * (80.0 * 80.0) / 6.0;
        return Example.builder("clothoid-iso", "CLOTHOID")
                .hens(0, 1)
                .pt(0, 0)
                .pt(80, y1)
                .chicken(0, 1, "MkClothoid")
                .iso(new Pt(0, 0), new Pt(1, 0), new Pt(0, 1), "100", "0", "50")
                .tau("TagClothoid")
                .build();
    }

    /**
     * Well-formed geodesic bags MkChord; τ = TagLineString.
     * Emit LINESTRING text + WKB 2. Not GEODESICSTRING / WKB 13.
     */
    static Example geodesicAsLineString() {
        return Example.builder("geodesic-as-ls", "LINESTRING")
                .hens(0, 1)
                .pt(0, 0)
                .pt(2, 0)
                .control(0, 0)
                .control(2, 0)
                .chicken(0, 1, "MkChord")
                .tau("TagLineString")
                .build();
    }
}
