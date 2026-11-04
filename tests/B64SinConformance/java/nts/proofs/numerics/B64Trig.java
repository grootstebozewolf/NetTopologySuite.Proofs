// Java port of the proved binary64 evaluators, operation for operation, as
// the C# port tests/B64SinConformance/B64Sin.cs:
//   theories-flocq/B64_Sin.v          b64_sin, sin_accept_b
//   theories-flocq/B64_Cos.v          b64_cos
//   theories-flocq/B64_ArcPoint.v     b64_arc_x, b64_arc_y, arc_accept_b
//   theories-flocq/B64_Fresnel.v      b64_fresnel_C, b64_fresnel_S, fresnel_accept_b
//   theories-flocq/B64_ClothoidMap.v  cm_Icos, cm_Isin, cm_accept
//   theories-flocq/B64_MarginFilter.v mf_decide, mf_seg_g, mf_seg_g_outcome
// Every expression is one binary64 round-to-nearest-even operation of the
// Rocq definition, in the same order.  Java double arithmetic is IEEE 754
// binary64 (strict since Java 17, JEP 306) and the JIT does not contract
// a*b+c into an FMA, so no Math.fma appears and none is introduced.
// AI assistance disclosure: AI-drafted; human review pending.
package nts.proofs.numerics;

import static nts.proofs.numerics.B64Constants.*;

import java.util.function.DoubleUnaryOperator;

public final class B64Trig {
    private B64Trig() { }

    private static final double[] SIN_COEFFS =
        { sp_c0, sp_c1, sp_c2, sp_c3, sp_c4, sp_c5, sp_c6, sp_c7, sp_c8, sp_c9, sp_c10 };
    private static final double[] COS_COEFFS =
        { cq_c0, cq_c1, cq_c2, cq_c3, cq_c4, cq_c5, cq_c6, cq_c7, cq_c8, cq_c9, cq_c10, cq_c11 };
    private static final double[] FRESNEL_C_COEFFS =
    {
        frc_c0, frc_c1, frc_c2, frc_c3, frc_c4, frc_c5, frc_c6, frc_c7, frc_c8, frc_c9,
        frc_c10, frc_c11, frc_c12, frc_c13, frc_c14, frc_c15, frc_c16, frc_c17, frc_c18, frc_c19,
    };
    private static final double[] FRESNEL_S_COEFFS =
    {
        frs_c0, frs_c1, frs_c2, frs_c3, frs_c4, frs_c5, frs_c6, frs_c7, frs_c8, frs_c9,
        frs_c10, frs_c11, frs_c12, frs_c13, frs_c14, frs_c15, frs_c16, frs_c17, frs_c18,
    };

    // B64_Horner.b64_horner: [c] -> c ; c :: cs -> fl(fl(horner cs z * z) + c)
    private static double horner(double[] cs, double z) {
        double p = cs[cs.length - 1];
        for (int k = cs.length - 2; k >= 0; k--) {
            double t = p * z;
            p = t + cs[k];
        }
        return p;
    }

    // sn_core r = fl(r * horner(fl(r * r)))
    private static double sinCore(double r) {
        double z = r * r;
        return r * horner(SIN_COEFFS, z);
    }

    // cs_core r = horner(fl(r * r))
    private static double cosCore(double r) {
        double z = r * r;
        return horner(COS_COEFFS, z);
    }

    // sn_red x k = fl(fl(x - fl(k * C1)) - fl(k * C2))
    private static double red(double x, double k) {
        double t1 = k * sn_C1;
        double r1 = x - t1;
        double t2 = k * sn_C2;
        return r1 - t2;
    }

    // sn_neg s = fl(0 - s)
    private static double neg(double s) {
        return 0.0 - s;
    }

    // sn_pos / cs_pos
    private static double pos(DoubleUnaryOperator core, double x) {
        if (x <= sn_T1) return core.applyAsDouble(x);
        if (x <= sn_T3) return neg(core.applyAsDouble(red(x, sn_one)));
        if (x <= sn_T5) return core.applyAsDouble(red(x, sn_two));
        return neg(core.applyAsDouble(red(x, sn_three)));
    }

    // sin_accept_b x = b64_le (-10) x && b64_le x 10
    public static boolean accept(double x) {
        return sn_mten <= x && x <= sn_ten;
    }

    public static double sin(double x) {
        return (0.0 <= x) ? pos(B64Trig::sinCore, x) : neg(pos(B64Trig::sinCore, neg(x)));
    }

    public static double cos(double x) {
        return (0.0 <= x) ? pos(B64Trig::cosCore, x) : pos(B64Trig::cosCore, neg(x));
    }

    // B64_ArcPoint
    private static boolean in(double x) {
        return ap_mcap <= x && x <= ap_cap;
    }

    public static boolean arcAccept(double cx, double cy, double r, double t) {
        return in(cx) && in(cy) && in(r) && accept(t);
    }

    public static double arcX(double cx, double r, double t) {
        double p = r * cos(t);
        return cx + p;
    }

    public static double arcY(double cy, double r, double t) {
        double p = r * sin(t);
        return cy + p;
    }

    // B64_Fresnel
    public static boolean fresnelAccept(double x) {
        return fr_mX <= x && x <= fr_X;
    }

    private static double frZ(double x) {
        double t = x * x;
        return t * t;
    }

    public static double fresnelC(double x) {
        return x * horner(FRESNEL_C_COEFFS, frZ(x));
    }

    public static double fresnelS(double x) {
        double w = x * (x * x);
        return w * horner(FRESNEL_S_COEFFS, frZ(x));
    }

    // B64_ClothoidMap
    private static double cmW(double a) {
        return cm_r2 * a;
    }

    private static double cmX(double a, double s) {
        return s / cmW(a);
    }

    public static boolean clothoidAccept(double a, double s) {
        return (cm_Alo <= a && a <= cm_cap) && (cm_mcap <= s && s <= cm_cap) && fresnelAccept(cmX(a, s));
    }

    public static double clothoidIcos(double a, double s) {
        return cmW(a) * fresnelC(cmX(a, s));
    }

    public static double clothoidIsin(boolean negate, double a, double s) {
        double v = cmW(a) * fresnelS(cmX(a, s));
        return negate ? neg(v) : v;
    }

    // B64_MarginFilter: mf_lt x y = b64_le x y && !(b64_le y x)
    private static boolean mfLt(double x, double y) {
        return x <= y && !(y <= x);
    }

    // mf_decide v thr: +1 POSITIVE, -1 NEGATIVE, 0 UNDECIDED
    public static int marginDecide(double v, double thr) {
        return mfLt(thr, v) ? 1 : mfLt(v, neg(thr)) ? -1 : 0;
    }

    public static double segG(double t) {
        return t - sin(t);
    }

    public static String segGOutcome(double t) {
        if (!accept(t)) return "DECLINE";
        double v = segG(t);
        int d = marginDecide(v, mf_seg_thr);
        String bits = String.format("%016x", Double.doubleToRawLongBits(v));
        return d > 0 ? "POSITIVE " + bits : d < 0 ? "NEGATIVE " + bits : "DECLINE";
    }
}
