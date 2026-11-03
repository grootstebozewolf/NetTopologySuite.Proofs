// Port of theories-flocq/B64_Sin.v : b64_sin / sin_accept_b, operation for
// operation.  Every line below is one binary64 round-to-nearest-even
// operation of the Rocq definition, in the same order; no FMA, no reordering
// (.NET does not contract a*b+c on its own).  The proved contract is
// B64_Sin.b64_sin_err_b: Accept(x) => |Sin(x) - sin x| <= 2^-49.
// AI assistance disclosure: AI-drafted; human review pending.
using static NTS.Proofs.Numerics.B64SinConstants;

namespace NTS.Proofs.Numerics;

public static class B64Sin
{
    // B64_SinPoly.sp_coeffs = [c0; ...; c10]
    private static readonly double[] Coeffs =
        { sp_c0, sp_c1, sp_c2, sp_c3, sp_c4, sp_c5, sp_c6, sp_c7, sp_c8, sp_c9, sp_c10 };

    // B64_Horner.b64_horner: [c] -> c ; c :: cs -> fl(fl(horner cs z * z) + c)
    private static double Horner(double z)
    {
        double p = Coeffs[10];
        for (int k = 9; k >= 0; k--)
        {
            double t = p * z;
            p = t + Coeffs[k];
        }
        return p;
    }

    // sn_core r = fl(r * horner(fl(r * r)))
    private static double Core(double r)
    {
        double z = r * r;
        return r * Horner(z);
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

    // sn_pos: b64_le x T is x <= T on finite inputs
    private static double Pos(double x)
    {
        if (x <= sn_T1) return Core(x);
        if (x <= sn_T3) return Neg(Core(Red(x, sn_one)));
        if (x <= sn_T5) return Core(Red(x, sn_two));
        return Neg(Core(Red(x, sn_three)));
    }

    // sin_accept_b x = b64_le (-10) x && b64_le x 10  (false on NaN, +-inf)
    public static bool Accept(double x) => sn_mten <= x && x <= sn_ten;

    // b64_sin x = if b64_le 0 x then sn_pos x else sn_neg (sn_pos (sn_neg x))
    public static double Sin(double x) => (0.0 <= x) ? Pos(x) : Neg(Pos(Neg(x)));
}
