package org.nts.proofs.intake;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Locale;

/**
 * First-slice intake answer. Mirrors {@code theories/IntakeWalker.v}.
 * Intake Decline is not cook {@code IDecline}.
 */
public final class IntakeResult {
    public enum Reason {
        ID_Empty,
        ID_BadPointCount,
        ID_GeodesicString,
        ID_SpiralCurve,
        ID_IsoClothoid,
        ID_MkOutOfScope,
        ID_CircGammaLeftover,
        ID_NotFirstSlice,
        ID_ParseFail
    }

    public static final class Point {
        public final double x;
        public final double y;

        public Point(double x, double y) {
            this.x = x;
            this.y = y;
        }

        @Override
        public String toString() {
            return String.format(Locale.ROOT, "%s %s", trim(x), trim(y));
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

    public static final class Bag {
        public final List<Integer> hens;
        public final List<Point> pts;
        public final List<Chicken> chickens;

        public Bag(List<Integer> hens, List<Point> pts, List<Chicken> chickens) {
            this.hens = Collections.unmodifiableList(new ArrayList<>(hens));
            this.pts = Collections.unmodifiableList(new ArrayList<>(pts));
            this.chickens = Collections.unmodifiableList(new ArrayList<>(chickens));
        }
    }

    public final Bag bag;
    public final Reason decline;

    private IntakeResult(Bag bag, Reason decline) {
        this.bag = bag;
        this.decline = decline;
    }

    public static IntakeResult bag(Bag bag) {
        return new IntakeResult(bag, null);
    }

    public static IntakeResult decline(Reason reason) {
        return new IntakeResult(null, reason);
    }

    public boolean isBag() {
        return bag != null;
    }

    public String wire() {
        if (!isBag()) {
            return "DECLINE " + decline.name();
        }
        StringBuilder sb = new StringBuilder("BAG");
        sb.append(" hens=");
        for (int i = 0; i < bag.hens.size(); i++) {
            if (i > 0) {
                sb.append(',');
            }
            sb.append(bag.hens.get(i));
        }
        sb.append(" pts=");
        for (int i = 0; i < bag.pts.size(); i++) {
            if (i > 0) {
                sb.append(';');
            }
            sb.append(bag.pts.get(i));
        }
        sb.append(" chickens=");
        for (int i = 0; i < bag.chickens.size(); i++) {
            if (i > 0) {
                sb.append(',');
            }
            sb.append(bag.chickens.get(i));
        }
        return sb.toString();
    }

    private static String trim(double v) {
        if (v == Math.rint(v) && Math.abs(v) < 1e12) {
            return Long.toString((long) v);
        }
        return Double.toString(v);
    }
}
