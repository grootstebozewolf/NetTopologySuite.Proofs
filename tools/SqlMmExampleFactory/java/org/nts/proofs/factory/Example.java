package org.nts.proofs.factory;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Structured bag/model matching {@code IntakeResult.Bag} vocabulary
 * (hens / pts / chickens + egg tags) plus the surface form needed to
 * invert intake. CIRCULARSTRING / CIRCLE store bag endpoints in
 * {@code pts} and the §5.1.67 control list in {@code controls}.
 *
 * τ(MkChord) = TagLineString — GEODESICSTRING is not a keyword here.
 *
 * claimId: none (tools). Mirrors tools/WktIntakeWalker; does not remint
 * Rocq emit inhabit ({@code ticket_sqlmm_factory_emit_qed_or_qex} stays QEX).
 */
public final class Example {
    public final String id;
    /** §5.1.67 display keyword (LINESTRING, not GEODESICSTRING). */
    public final String keyword;
    public final boolean empty;
    public final boolean point;
    public final boolean lineString;
    public final boolean circularString;
    public final boolean circle;
    public final boolean compound;
    public final boolean clothoid;
    public final boolean jtsClothoid;
    public final boolean affineEmpty;

    /** Intake hens. */
    public final List<Integer> hens;
    /** Intake bag endpoints. */
    public final List<Pt> pts;
    /** Intake chickens (src-dst:egg). */
    public final List<Chicken> chickens;
    /** WKT / WKB control points (may be richer than {@code pts}). */
    public final List<Pt> controls;
    public final List<Example> children;

    public final String tau;
    public final String k0;
    public final String k1;
    public final String L;
    public final Pt location;
    public final Pt e1;
    public final Pt e2;
    public final String scaleFactor;
    public final String startDistance;
    public final String endDistance;
    /** Non-null ⇒ bagWire is {@code DECLINE <reason>}. */
    public final String decline;

    private Example(Builder b) {
        this.id = b.id;
        this.keyword = b.keyword;
        this.empty = b.empty;
        this.point = "POINT".equals(b.keyword);
        this.lineString = "LINESTRING".equals(b.keyword);
        this.circularString = "CIRCULARSTRING".equals(b.keyword);
        this.circle = "CIRCLE".equals(b.keyword);
        this.compound = "COMPOUNDCURVE".equals(b.keyword);
        this.clothoid = "CLOTHOID".equals(b.keyword);
        this.jtsClothoid = b.jtsClothoid;
        this.affineEmpty = b.affineEmpty;
        this.hens = Collections.unmodifiableList(new ArrayList<>(b.hens));
        this.pts = Collections.unmodifiableList(new ArrayList<>(b.pts));
        this.chickens = Collections.unmodifiableList(new ArrayList<>(b.chickens));
        this.controls = Collections.unmodifiableList(new ArrayList<>(b.controls));
        this.children = Collections.unmodifiableList(new ArrayList<>(b.children));
        this.tau = b.tau;
        this.k0 = b.k0;
        this.k1 = b.k1;
        this.L = b.L;
        this.location = b.location;
        this.e1 = b.e1;
        this.e2 = b.e2;
        this.scaleFactor = b.scaleFactor;
        this.startDistance = b.startDistance;
        this.endDistance = b.endDistance;
        this.decline = b.decline;
    }

    public static Builder builder(String id, String keyword) {
        return new Builder(id, keyword);
    }

    /**
     * Same wire as {@code IntakeResult.wire()} on a bag, or
     * {@code DECLINE ID_Empty} for EMPTY surface forms (intake mapper).
     */
    public String bagWire() {
        if (decline != null) {
            return "DECLINE " + decline;
        }
        if (empty) {
            return "DECLINE ID_Empty";
        }
        StringBuilder sb = new StringBuilder("BAG");
        sb.append(" hens=");
        for (int i = 0; i < hens.size(); i++) {
            if (i > 0) {
                sb.append(',');
            }
            sb.append(hens.get(i));
        }
        sb.append(" pts=");
        for (int i = 0; i < pts.size(); i++) {
            if (i > 0) {
                sb.append(';');
            }
            sb.append(pts.get(i));
        }
        sb.append(" chickens=");
        for (int i = 0; i < chickens.size(); i++) {
            if (i > 0) {
                sb.append(',');
            }
            sb.append(chickens.get(i));
        }
        return sb.toString();
    }

    public static final class Pt {
        public final String x;
        public final String y;
        public final double xd;
        public final double yd;

        public Pt(double x, double y) {
            this.xd = x;
            this.yd = y;
            this.x = Hex.trim(x);
            this.y = Hex.trim(y);
        }

        @Override
        public String toString() {
            return x + " " + y;
        }
    }

    public static final class Chicken {
        public final int src;
        public final int dst;
        public final String egg;

        public Chicken(int src, int dst, String egg) {
            this.src = src;
            this.dst = dst;
            this.egg = egg;
        }

        @Override
        public String toString() {
            return src + "-" + dst + ":" + egg;
        }
    }

    public static final class Builder {
        final String id;
        final String keyword;
        boolean empty;
        boolean jtsClothoid;
        boolean affineEmpty;
        final List<Integer> hens = new ArrayList<>();
        final List<Pt> pts = new ArrayList<>();
        final List<Chicken> chickens = new ArrayList<>();
        final List<Pt> controls = new ArrayList<>();
        final List<Example> children = new ArrayList<>();
        String tau = "TagLineString";
        String k0;
        String k1;
        String L;
        Pt location;
        Pt e1;
        Pt e2;
        String scaleFactor;
        String startDistance;
        String endDistance;
        String decline;

        Builder(String id, String keyword) {
            this.id = id;
            this.keyword = keyword;
        }

        public Builder empty() {
            this.empty = true;
            return this;
        }

        public Builder decline(String reason) {
            this.decline = reason;
            return this;
        }

        public Builder hens(int... hs) {
            for (int h : hs) {
                hens.add(h);
            }
            return this;
        }

        public Builder pt(double x, double y) {
            pts.add(new Pt(x, y));
            return this;
        }

        public Builder control(double x, double y) {
            controls.add(new Pt(x, y));
            return this;
        }

        public Builder chicken(int src, int dst, String egg) {
            chickens.add(new Chicken(src, dst, egg));
            return this;
        }

        public Builder child(Example c) {
            children.add(c);
            return this;
        }

        public Builder tau(String t) {
            this.tau = t;
            return this;
        }

        public Builder jts(String k0, String k1, String L) {
            this.jtsClothoid = true;
            this.k0 = k0;
            this.k1 = k1;
            this.L = L;
            return this;
        }

        public Builder iso(Pt location, Pt e1, Pt e2, String scale, String start, String end) {
            this.jtsClothoid = false;
            this.location = location;
            this.e1 = e1;
            this.e2 = e2;
            this.scaleFactor = scale;
            this.startDistance = start;
            this.endDistance = end;
            return this;
        }

        public Builder isoEmpty(String scale, String start, String end) {
            this.jtsClothoid = false;
            this.affineEmpty = true;
            this.scaleFactor = scale;
            this.startDistance = start;
            this.endDistance = end;
            return this;
        }

        public Example build() {
            if (!empty && controls.isEmpty()
                    && !"COMPOUNDCURVE".equals(keyword)
                    && !"CLOTHOID".equals(keyword)) {
                controls.addAll(pts);
            }
            return new Example(this);
        }
    }
}
