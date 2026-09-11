package org.nts.proofs.intake;

import java.util.ArrayList;
import java.util.List;
import org.nts.proofs.intake.IntakeResult.Bag;
import org.nts.proofs.intake.IntakeResult.Chicken;
import org.nts.proofs.intake.IntakeResult.Point;
import org.nts.proofs.intake.IntakeResult.Reason;
import org.nts.proofs.intake.gen.wktParser;
import org.nts.proofs.intake.gen.wktParserBaseVisitor;

/**
 * ANTLR visitor: tagged CST → first-slice SHC bag | named Intake Decline.
 * Mapping table is the same as {@code theories/IntakeWalker.v}.
 * No noding, no split(t), no snap, no silent chord demote.
 */
public final class IntakeVisitor extends wktParserBaseVisitor<IntakeResult> {

    static final Point P50 = new Point(5, 0);
    static final Point P05 = new Point(0, 5);
    static final Point PM50 = new Point(-5, 0);

    @Override
    public IntakeResult visitFile_(wktParser.File_Context ctx) {
        if (ctx.geometry().isEmpty()) {
            return IntakeResult.decline(Reason.ID_Empty);
        }
        if (ctx.geometry().size() != 1) {
            return IntakeResult.decline(Reason.ID_NotFirstSlice);
        }
        return visit(ctx.geometry(0));
    }

    @Override
    public IntakeResult visitPointGeometry(wktParser.PointGeometryContext ctx) {
        if (ctx.dim() != null) {
            return IntakeResult.decline(Reason.ID_NotFirstSlice);
        }
        if (ctx.pointText().EMPTY_() != null || ctx.pointText().point() == null) {
            return IntakeResult.decline(Reason.ID_Empty);
        }
        List<Point> pts = pointsOf(ctx.pointText().point());
        if (pts.isEmpty()) {
            return IntakeResult.decline(Reason.ID_Empty);
        }
        return IntakeResult.bag(new Bag(List.of(0), pts, List.of()));
    }

    @Override
    public IntakeResult visitLineStringGeometry(wktParser.LineStringGeometryContext ctx) {
        if (ctx.dim() != null) {
            return IntakeResult.decline(Reason.ID_NotFirstSlice);
        }
        return mapLineString(pointsOf(ctx.lineStringText()));
    }

    @Override
    public IntakeResult visitCircularStringGeometry(wktParser.CircularStringGeometryContext ctx) {
        if (ctx.dim() != null) {
            return IntakeResult.decline(Reason.ID_NotFirstSlice);
        }
        return mapCircularString(pointsOf(ctx.lineStringText()));
    }

    @Override
    public IntakeResult visitCircleGeometry(wktParser.CircleGeometryContext ctx) {
        if (ctx.dim() != null) {
            return IntakeResult.decline(Reason.ID_NotFirstSlice);
        }
        return mapCircle(pointsOf(ctx.lineStringText()));
    }

    @Override
    public IntakeResult visitCompoundCurveGeometry(wktParser.CompoundCurveGeometryContext ctx) {
        if (ctx.dim() != null) {
            return IntakeResult.decline(Reason.ID_NotFirstSlice);
        }
        if (ctx.EMPTY_() != null || ctx.compoundCurveMember().isEmpty()) {
            return IntakeResult.decline(Reason.ID_Empty);
        }
        IntakeResult acc = null;
        IntakeResult firstDecline = null;
        for (wktParser.CompoundCurveMemberContext member : ctx.compoundCurveMember()) {
            IntakeResult next = visit(member.curveMember());
            if (!next.isBag()) {
                if (next.decline == Reason.ID_IsoClothoid) {
                    return next;
                }
                if (firstDecline == null) {
                    firstDecline = next;
                }
                continue;
            }
            acc = acc == null ? next : IntakeResult.bag(append(acc.bag, next.bag));
        }
        if (firstDecline != null) {
            return firstDecline;
        }
        return acc == null ? IntakeResult.decline(Reason.ID_Empty) : acc;
    }

    @Override
    public IntakeResult visitCurveMember(wktParser.CurveMemberContext ctx) {
        if (ctx.lineStringText() != null) {
            return mapLineString(pointsOf(ctx.lineStringText()));
        }
        if (ctx.circularStringGeometry() != null) {
            return visit(ctx.circularStringGeometry());
        }
        if (ctx.circleGeometry() != null) {
            return visit(ctx.circleGeometry());
        }
        if (ctx.geodesicStringGeometry() != null) {
            return IntakeResult.decline(Reason.ID_GeodesicString);
        }
        if (ctx.clothoidGeometry() != null) {
            return visit(ctx.clothoidGeometry());
        }
        if (ctx.spiralCurveGeometry() != null) {
            return IntakeResult.decline(Reason.ID_SpiralCurve);
        }
        if (ctx.compoundCurveGeometry() != null) {
            return visit(ctx.compoundCurveGeometry());
        }
        return IntakeResult.decline(Reason.ID_NotFirstSlice);
    }

    @Override
    public IntakeResult visitClothoidGeometry(wktParser.ClothoidGeometryContext ctx) {
        wktParser.ClothoidTextContext text = ctx.clothoidText();
        if (text.EMPTY_() != null) {
            return IntakeResult.decline(Reason.ID_Empty);
        }
        if (text.referenceLocationText() != null) {
            return IntakeResult.decline(Reason.ID_IsoClothoid);
        }
        return IntakeResult.decline(Reason.ID_MkOutOfScope);
    }

    @Override
    public IntakeResult visitGeodesicStringGeometry(wktParser.GeodesicStringGeometryContext ctx) {
        return IntakeResult.decline(Reason.ID_GeodesicString);
    }

    @Override
    public IntakeResult visitSpiralCurveGeometry(wktParser.SpiralCurveGeometryContext ctx) {
        return IntakeResult.decline(Reason.ID_SpiralCurve);
    }

    @Override
    public IntakeResult visitGeometry(wktParser.GeometryContext ctx) {
        return visitChildren(ctx);
    }

    @Override
    protected IntakeResult defaultResult() {
        return IntakeResult.decline(Reason.ID_NotFirstSlice);
    }

    @Override
    protected IntakeResult aggregateResult(IntakeResult aggregate, IntakeResult nextResult) {
        if (nextResult != null && (aggregate == null || !aggregate.isBag()
                && nextResult.decline != Reason.ID_NotFirstSlice)) {
            return nextResult;
        }
        return aggregate == null ? defaultResult() : aggregate;
    }

    static IntakeResult mapLineString(List<Point> pts) {
        if (pts.isEmpty()) {
            return IntakeResult.decline(Reason.ID_Empty);
        }
        if (pts.size() < 2) {
            return IntakeResult.decline(Reason.ID_BadPointCount);
        }
        List<Integer> hens = hens(pts.size());
        List<Chicken> chickens = new ArrayList<>();
        for (int i = 0; i < pts.size() - 1; i++) {
            chickens.add(new Chicken(i, i + 1, "MkChord"));
        }
        return IntakeResult.bag(new Bag(hens, pts, chickens));
    }

    static IntakeResult mapCircularString(List<Point> pts) {
        if (pts.isEmpty()) {
            return IntakeResult.decline(Reason.ID_Empty);
        }
        if (pts.size() != 3) {
            return IntakeResult.decline(Reason.ID_BadPointCount);
        }
        Point a = pts.get(0);
        Point b = pts.get(1);
        Point c = pts.get(2);
        if (eq(a, P50) && eq(c, P05)) {
            return circBag(List.of(P50, P05), "MkCirc:quarter");
        }
        if (eq(a, P50) && eq(b, P05) && eq(c, P50)) {
            return circBag(List.of(P50, P50), "MkCirc:full");
        }
        return IntakeResult.decline(Reason.ID_CircGammaLeftover);
    }

    static IntakeResult mapCircle(List<Point> pts) {
        if (pts.isEmpty()) {
            return IntakeResult.decline(Reason.ID_Empty);
        }
        if (pts.size() != 3) {
            return IntakeResult.decline(Reason.ID_BadPointCount);
        }
        if (eq(pts.get(0), P50) && eq(pts.get(2), PM50)) {
            return circBag(List.of(P50, PM50), "MkCirc:full");
        }
        return IntakeResult.decline(Reason.ID_CircGammaLeftover);
    }

    private static IntakeResult circBag(List<Point> pts, String egg) {
        return IntakeResult.bag(new Bag(List.of(0, 1), pts, List.of(new Chicken(0, 1, egg))));
    }

    private static Bag append(Bag a, Bag b) {
        int off = a.hens.size();
        List<Integer> hens = new ArrayList<>(a.hens);
        for (int h : b.hens) {
            hens.add(off + h);
        }
        List<Point> pts = new ArrayList<>(a.pts);
        pts.addAll(b.pts);
        List<Chicken> chickens = new ArrayList<>(a.chickens);
        for (Chicken c : b.chickens) {
            chickens.add(new Chicken(off + c.src, off + c.dst, c.egg));
        }
        return new Bag(hens, pts, chickens);
    }

    private static List<Integer> hens(int n) {
        List<Integer> hs = new ArrayList<>(n);
        for (int i = 0; i < n; i++) {
            hs.add(i);
        }
        return hs;
    }

    private static List<Point> pointsOf(wktParser.LineStringTextContext ctx) {
        if (ctx == null || ctx.EMPTY_() != null) {
            return List.of();
        }
        return pointsOf(ctx.point());
    }

    private static List<Point> pointsOf(wktParser.PointContext ctx) {
        return ctx == null ? List.of() : pointsOf(List.of(ctx));
    }

    private static List<Point> pointsOf(List<wktParser.PointContext> ctxs) {
        List<Point> pts = new ArrayList<>();
        if (ctxs == null) {
            return pts;
        }
        for (wktParser.PointContext p : ctxs) {
            List<wktParser.OrdinateContext> ords = p.ordinate();
            if (ords.size() < 2) {
                continue;
            }
            pts.add(new Point(parseOrd(ords.get(0)), parseOrd(ords.get(1))));
        }
        return pts;
    }

    private static double parseOrd(wktParser.OrdinateContext ctx) {
        if (ctx.NAN_() != null) {
            return Double.NaN;
        }
        if (ctx.INF_() != null) {
            return Double.POSITIVE_INFINITY;
        }
        if (ctx.NEG_INF_() != null) {
            return Double.NEGATIVE_INFINITY;
        }
        return Double.parseDouble(ctx.DECIMAL().getText());
    }

    private static boolean eq(Point a, Point b) {
        return a.x == b.x && a.y == b.y;
    }
}
