// C# port of the Rocq-proved binary64 de Casteljau evaluator.
//
//   Rocq source of record : theories-flocq/B64_DeCasteljauEval.v  (dc_eval)
//                           theories-flocq/B64_DeCasteljau.v      (dcF, dc_node)
//   Oracle (extracted)    : oracle_bin mode B64_DECASTELJAU
//   Conformance           : tests/B64DeCasteljauConformance (bit identity)
//
// ---------------------------------------------------------------------------
// CONTRACT  (this is the record of what the proof does and does not cover)
// ---------------------------------------------------------------------------
// Eval(controls, t) returns one of
//   CERTIFIED <value>
//   DECLINE_EMPTY            no controls
//   DECLINE_DEGREE           more than 1001 controls (degree n > 1000)
//   DECLINE_NONFINITE        t or a control is NaN / +-Inf
//   DECLINE_PARAM            t is not in [0, 1]
//   DECLINE_OVERFLOW_GUARD   some |control| > 2^500
// checked in exactly that order (mirrors dc_eval).
//
// Covering theorem  : B64_DeCasteljauEval.v : dc_eval_certified, which applies
//   B64_DeCasteljau.v : b64_decasteljau_err_fl.  For a CERTIFIED value v of a
//   degree-n net (n = Length - 1) and ANY M with |b_i| <= M <= 2^500:
//     v is finite and
//     |v - exact| <= ((1+k)^n - 1) M + 2^-1075 (3+2u) n (1+k)^n,
//     u = 2^-53, k = eta + (1+eta)(2u+u^2), eta = u + 2^-1075,
//   where `exact` is de Casteljau in R with weights (1-t, t) of the same
//   control values (= the Bernstein sum, B64_BezierStability.v : dcR_bern).
//   The weight policy is s = fl(1 - t) (`double s = 1.0 - t`).
//   The caps (degree 1000, |b_i| <= 2^500) are conservative sufficient
//   conditions for the theorem's overflow guard (dc_guard_ok); they are not
//   the theorem's own hypotheses.
//
// EXECUTION-TRACE CONTRACT.  The proved program rounds three times per node:
//   a = fl(s*x);  c = fl(t*y);  node = fl(a + c).
// A fused multiply-add computes fl(s*x + c) in one rounding and is a DIFFERENT
// program for which the theorem above is not stated.  This class therefore
//   * never calls Math.FusedMultiplyAdd / FMA intrinsics;
//   * keeps the two products in separate locals before the sum;
//   * is checked by the conformance harness against the extracted oracle on a
//     corpus in which a large share of nodes are FMA-sensitive (the harness
//     counts how many certified results change under each FMA variant, so a
//     JIT/compiler that contracted the expression would fail bit identity).
// An FMA variant would need its own theorem and its own oracle mode.
//
// NOT claimed: that GEOS, NTS or any consumer uses this evaluator; anything
// about NURBS / rational weights / de Boor; any behaviour outside the domain
// above (every such input declines).
//
// AI assistance disclosure: AI-drafted; human review pending.
using System.Runtime.CompilerServices;

namespace NTS.Proofs.Numerics;

public static class B64DeCasteljau
{
    public const int MaxLen = 1001;
    static readonly double Cap = Math.ScaleB(1.0, 500);   // 2^500, exact
    const double FMax = double.MaxValue;      // (2^53 - 1) 2^971

    // Finite by comparison, as in dc_fin_b (rejects NaN and both infinities).
    static bool Fin(double x) => -FMax <= x && x <= FMax;

    /// <summary>Returns the outcome string of dc_eval; <paramref name="value"/>
    /// is meaningful only when the result is "CERTIFIED".</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    public static string Eval(double[] controls, double t, out double value)
    {
        value = double.NaN;
        int len = controls.Length;
        if (len == 0) return "DECLINE_EMPTY";
        if (len > MaxLen) return "DECLINE_DEGREE";
        bool fin = Fin(t);
        for (int i = 0; fin && i < len; i++) fin = Fin(controls[i]);
        if (!fin) return "DECLINE_NONFINITE";
        if (!(0.0 <= t && t <= 1.0)) return "DECLINE_PARAM";
        for (int i = 0; i < len; i++)
            if (!(-Cap <= controls[i] && controls[i] <= Cap)) return "DECLINE_OVERFLOW_GUARD";

        double s = 1.0 - t;                    // b64_minus dc_one t  (eta = u + 2^-1075)
        var row = (double[])controls.Clone();
        for (int round = 1; round < len; round++)          // n = len - 1 rounds
            for (int i = 0; i + round < len; i++)          // node(row[i], row[i+1]), old values
            {
                double a = s * row[i];                     // fl(s x)
                double c = t * row[i + 1];                 // fl(t y)
                row[i] = a + c;                            // fl(a + c): no FMA
            }
        value = row[0];                                    // hd of the last row
        return "CERTIFIED";
    }
}
