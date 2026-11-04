// Port of theories-flocq/B64_Sin.v : b64_sin / sin_accept_b and
// theories-flocq/B64_Cos.v : b64_cos and theories-flocq/B64_ArcPoint.v :
// b64_arc_x / b64_arc_y / arc_accept_b and theories-flocq/B64_Fresnel.v :
// b64_fresnel_C / b64_fresnel_S / fresnel_accept_b and
// theories-flocq/B64_ClothoidMap.v : cm_Icos / cm_Isin / cm_accept and
// theories-flocq/B64_MarginFilter.v : mf_decide / mf_seg_g / mf_seg_g_outcome,
// operation for operation.  Every line
// below is one binary64 round-to-nearest-even operation of the Rocq
// definition, in the same order; no FMA, no reordering (.NET does not
// contract a*b+c on its own).  Proved contracts: B64_Sin.b64_sin_err_b and
// B64_Cos.b64_cos_err_b: Accept(x) => |Sin(x) - sin x|, |Cos(x) - cos x|
// <= 2^-49.
// AI assistance disclosure: AI-drafted; human review pending.
using static NTS.Proofs.Numerics.B64SinConstants;

namespace NTS.Proofs.Numerics;

public static class B64Sin
{
    // B64_SinPoly.sp_coeffs = [c0; ...; c10]
    private static readonly double[] SinCoeffs =
        { sp_c0, sp_c1, sp_c2, sp_c3, sp_c4, sp_c5, sp_c6, sp_c7, sp_c8, sp_c9, sp_c10 };

    // B64_CosPoly.cq_coeffs = [c0; ...; c11]
    private static readonly double[] CosCoeffs =
        { cq_c0, cq_c1, cq_c2, cq_c3, cq_c4, cq_c5, cq_c6, cq_c7, cq_c8, cq_c9, cq_c10, cq_c11 };

    // B64_Horner.b64_horner: [c] -> c ; c :: cs -> fl(fl(horner cs z * z) + c)
    private static double Horner(double[] cs, double z)
    {
        double p = cs[cs.Length - 1];
        for (int k = cs.Length - 2; k >= 0; k--)
        {
            double t = p * z;
            p = t + cs[k];
        }
        return p;
    }

    // sn_core r = fl(r * horner(fl(r * r)))
    private static double SinCore(double r)
    {
        double z = r * r;
        return r * Horner(SinCoeffs, z);
    }

    // cs_core r = horner(fl(r * r))
    private static double CosCore(double r)
    {
        double z = r * r;
        return Horner(CosCoeffs, z);
    }

    // sn_red x k = fl(fl(x - fl(k * C1)) - fl(k * C2))
    private static double Red(double x, double k)
    {
        double t1 = k * sn_C1;
        double r1 = x - t1;
        double t2 = k * sn_C2;
        return r1 - t2;
    }

    // sn_neg s = fl(0 - s), hz_zero = +0
    private static double Neg(double s) => 0.0 - s;

    // sn_pos / cs_pos: b64_le x T is x <= T on finite inputs
    private static double Pos(Func<double, double> core, double x)
    {
        if (x <= sn_T1) return core(x);
        if (x <= sn_T3) return Neg(core(Red(x, sn_one)));
        if (x <= sn_T5) return core(Red(x, sn_two));
        return Neg(core(Red(x, sn_three)));
    }

    // sin_accept_b x = b64_le (-10) x && b64_le x 10  (false on NaN, +-inf)
    public static bool Accept(double x) => sn_mten <= x && x <= sn_ten;

    // b64_sin x = if b64_le 0 x then sn_pos x else sn_neg (sn_pos (sn_neg x))
    public static double Sin(double x) => (0.0 <= x) ? Pos(SinCore, x) : Neg(Pos(SinCore, Neg(x)));

    // b64_cos x = if b64_le 0 x then cs_pos x else cs_pos (sn_neg x)
    public static double Cos(double x) => (0.0 <= x) ? Pos(CosCore, x) : Pos(CosCore, Neg(x));

    // B64_ArcPoint.ap_in x = b64_le (-2^998) x && b64_le x 2^998
    private static bool In(double x) => ap_mcap <= x && x <= ap_cap;

    // B64_ArcPoint.arc_accept_b cx cy r t
    public static bool ArcAccept(double cx, double cy, double r, double t) =>
        In(cx) && In(cy) && In(r) && Accept(t);

    // B64_ArcPoint.b64_arc_x cx r t = fl(cx + fl(r * b64_cos t)), b64_arc_y likewise
    public static double ArcX(double cx, double r, double t) { double p = r * Cos(t); return cx + p; }
    public static double ArcY(double cy, double r, double t) { double p = r * Sin(t); return cy + p; }

    // B64_FresnelPoly.frc_coeffs / frs_coeffs
    private static readonly double[] FresnelCCoeffs =
    {
        frc_c0, frc_c1, frc_c2, frc_c3, frc_c4, frc_c5, frc_c6, frc_c7, frc_c8, frc_c9,
        frc_c10, frc_c11, frc_c12, frc_c13, frc_c14, frc_c15, frc_c16, frc_c17, frc_c18, frc_c19,
    };
    private static readonly double[] FresnelSCoeffs =
    {
        frs_c0, frs_c1, frs_c2, frs_c3, frs_c4, frs_c5, frs_c6, frs_c7, frs_c8, frs_c9,
        frs_c10, frs_c11, frs_c12, frs_c13, frs_c14, frs_c15, frs_c16, frs_c17, frs_c18,
    };

    // B64_Fresnel.fresnel_accept_b x = b64_le (-5/2) x && b64_le x (5/2)
    public static bool FresnelAccept(double x) => fr_mX <= x && x <= fr_X;

    // fr_t x = fl(x * x); fr_z x = fl(fr_t x * fr_t x)
    private static double FrZ(double x) { double t = x * x; return t * t; }

    // b64_fresnel_C x = fl(x * horner(frc, fr_z x))
    public static double FresnelC(double x) => x * Horner(FresnelCCoeffs, FrZ(x));

    // b64_fresnel_S x = fl(fl(x * fr_t x) * horner(frs, fr_z x))
    public static double FresnelS(double x) { double w = x * (x * x); return w * Horner(FresnelSCoeffs, FrZ(x)); }

    // B64_ClothoidMap: cm_w A = fl(fl(sqrt 2) * A); cm_x A s = fl(s / cm_w A)
    private static double CmW(double a) => cm_r2 * a;
    private static double CmX(double a, double s) => s / CmW(a);

    // cm_accept A s = (2^-500 <= A <= 2^500) && (|s| <= 2^500) && fresnel_accept_b (cm_x A s)
    public static bool ClothoidAccept(double a, double s) =>
        (cm_Alo <= a && a <= cm_cap) && (cm_mcap <= s && s <= cm_cap) && FresnelAccept(CmX(a, s));

    // cm_Icos A s = fl(cm_w A * b64_fresnel_C (cm_x A s))
    public static double ClothoidIcos(double a, double s) => CmW(a) * FresnelC(CmX(a, s));

    // cm_Isin neg A s = +-fl(cm_w A * b64_fresnel_S (cm_x A s)), negation as fl(0 - v)
    public static double ClothoidIsin(bool neg, double a, double s)
    {
        double v = CmW(a) * FresnelS(CmX(a, s));
        return neg ? Neg(v) : v;
    }

    // B64_MarginFilter.mf_lt x y = b64_le x y && !(b64_le y x)  (false on NaN)
    private static bool MfLt(double x, double y) => x <= y && !(y <= x);

    // mf_decide v thr: +1 POSITIVE, -1 NEGATIVE, 0 UNDECIDED
    public static int MarginDecide(double v, double thr) =>
        MfLt(thr, v) ? 1 : MfLt(v, Neg(thr)) ? -1 : 0;

    // mf_seg_g t = fl(t - b64_sin t)
    public static double SegG(double t) => t - Sin(t);

    // mf_seg_g_outcome t = mf_policy MF_DeclineFallback (sin_accept_b t) (mf_decide (mf_seg_g t) 2^-48):
    // "POSITIVE v" / "NEGATIVE v" / "DECLINE"
    public static string SegGOutcome(double t)
    {
        if (!Accept(t)) return "DECLINE";
        double v = SegG(t);
        int d = MarginDecide(v, mf_seg_thr);
        string bits = unchecked((ulong)BitConverter.DoubleToInt64Bits(v)).ToString("x16");
        return d > 0 ? "POSITIVE " + bits : d < 0 ? "NEGATIVE " + bits : "DECLINE";
    }
}
