(** * ArcSinglePeak — the exact remaining geometric seam for #64 (arc point-distance)

    On a circle, squared distance to P is affine-DECREASING in the dot product
    <P-O, Y-O>.  So the nearest on-arc point to P is wherever that dot is
    largest; when the radial foot (the global dot-maximiser) lies OUTSIDE the
    directed sweep, that maximum over the arc is attained at an ENDPOINT.

    This file BANKS the reusable circle/dot monotonicity helpers (§1, all Qed),
    then ISOLATES the one residual planar inequality (§2) — the "single-peak dot
    bound".  The metric seam `point_to_arc_dist_fallback_ends_lower` is
    discharged in `ArcPointDistance.v` by reducing it to §2, so the only
    remaining Tier-3 obligation is the crisp planar fact below — no metric
    residue.

    Status of §2 (PROVED, 2026-07-01):
      - The chord-frame reduction below is now a full `Qed`.  The earlier
        obstruction (`nra` "cannot find witness"; `psatz R 4` needing the absent
        CSDP solver) is avoided entirely: in the L-scaled chord frame the
        peak-side hypothesis becomes a sign test on one coordinate, and a tangent
        bound (`tangent_E`) plus a squared-magnitude comparison (`need_bound`,
        by sign cases) close the scalar core with only ring/lra/nra/field.
      - The statement gained the hypothesis `0 < dist S E`: without it the bound
        is FALSE at S = E (e.g. O=(0,0), S=E=(-1,0), r=1, P=X=(1,0) gives
        gdot = 1 > -1 = Rmax).  Every caller supplies it via `valid_arc`.

    Translates directly to the NTS CircularString / point-to-arc distance
    fallback guard.  Pure-R; §1 helpers and §2 are classical-reals trio only. *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance ArcDistance.

Local Open Scope R_scope.

(* The center-based dot product <P-O, Y-O>, inline in coordinates (ring-friendly). *)
Definition gdot (O P Y : Point) : R :=
  (px P - px O) * (px Y - px O) + (py P - py O) * (py Y - py O).

(* signed side of chord SE: cross (E-S) (Y-S). *)
Definition side (S E Y : Point) : R :=
  (px E - px S) * (py Y - py S) - (py E - py S) * (px Y - px S).

(* ------------------------------------------------------------------ *)
(* §1  Banked reductions (Qed, reusable).                             *)
(* ------------------------------------------------------------------ *)

(* Law of cosines about the center. *)
Lemma dist2_via_center_dot : forall O P Y,
  dist_sq P Y = dist_sq P O + dist_sq O Y - 2 * gdot O P Y.
Proof. intros O P Y. unfold dist_sq, gdot. ring. Qed.

(* On a common circle, larger dot ==> nearer to P. *)
Lemma circle_dist_le_of_dot_ge : forall O P Y Z r,
  dist O Y = r -> dist O Z = r ->
  gdot O P Z <= gdot O P Y ->
  dist P Y <= dist P Z.
Proof.
  intros O P Y Z r HY HZ Hdot.
  unfold dist. apply sqrt_le_1_alt.
  pose proof (dist2_via_center_dot O P Y) as EY.
  pose proof (dist2_via_center_dot O P Z) as EZ.
  assert (HsqY : dist_sq O Y = r * r).
  { pose proof (dist_mul_self O Y) as H. rewrite HY in H. lra. }
  assert (HsqZ : dist_sq O Z = r * r).
  { pose proof (dist_mul_self O Z) as H. rewrite HZ in H. lra. }
  rewrite EY, EZ, HsqY, HsqZ. lra.
Qed.

(* Opposite-sign helper: same-side product positive + cross product nonpositive
   forces the remaining product nonpositive (used to turn "X in span, foot not in
   span" into the opposite-sides hypothesis of the core). *)
Lemma sign_opp : forall m x f : R, 0 < m * x -> m * f <= 0 -> x * f <= 0.
Proof.
  intros m x f Hmx Hmf.
  destruct (Rtotal_order m 0) as [Hm | [Hm | Hm]].
  - nra.
  - subst m; lra.
  - nra.
Qed.

(* ------------------------------------------------------------------ *)
(* §2  The isolated planar single-peak dot bound.                     *)
(*                                                                    *)
(* S,E,X on the circle of center O radius r; X and the radial foot F  *)
(* on opposite (closed) sides of chord SE  ==>  the dot at X is        *)
(* bounded by the larger endpoint dot.                                *)
(*                                                                    *)
(* CHORD-FRAME REDUCTION (the documented route to a hand proof):       *)
(*   frame: M=midpoint SE, t=normalize(E-S), n=perp t; S=(-h,0),       *)
(*   E=(h,0), O=(0,d); X=(a,b) with a^2 = h^2 + 2*b*d - b^2 and        *)
(*   h^2+d^2=r^2; (pt,pn)=P-O in frame, q=|P-O|.  X in span gives      *)
(*   b*d <= 0; foot outside gives d*(q*d + r*pn) >= 0.  Goal reduces   *)
(*   to  a*pt + b*pn <= h*Rabs pt  (the irreducible scalar core).      *)
(*                                                                    *)
(* PROVED (chord-frame reduction, three-axiom).  The reduction above is now a
   full proof: work in the (unnormalised, L-scaled) chord frame where the chord
   SE lies on the horizontal axis, so `side S E Y` is proportional to Y's
   perpendicular coordinate.  Two ingredients close the scalar core:
     - the tangent bound  <E-O, X-E> <= 0  (Cauchy-Schwarz: the circle lies on
       one side of its tangent at E);
     - `need_bound`: the opposite-sides / radial-foot hypothesis forces the sign
       of  pa*d + h*beta  (a squared-magnitude comparison, cleared by cases).
   Reflecting the chord frame (S <-> E) handles the second endpoint.  The extra
   hypothesis `0 < dist S E` rules out the degenerate S = E (where the bound is
   false); the calling context supplies it from `valid_arc`.                    *)

(* §2a  Scalar chord-frame core (banked, all Qed).                    *)

(* From a squared-magnitude bound to the linear sign, opposite-sign branch. *)
Lemma sq_to_lin_pos :
  forall h d pa beta : R,
    0 < h -> 0 <= pa -> 0 < d -> beta <= 0 ->
    (pa*pa)*(d*d) <= (h*h)*(beta*beta) -> pa*d + h*beta <= 0.
Proof. intros. assert (0 <= pa*d) by nra. assert (h*beta <= 0) by nra. nra. Qed.

Lemma sq_to_lin_neg :
  forall h d pa beta : R,
    0 < h -> 0 <= pa -> d <= 0 -> 0 < beta ->
    (h*h)*(beta*beta) <= (pa*pa)*(d*d) -> pa*d + h*beta <= 0.
Proof. intros. assert (pa*d <= 0) by nra. assert (0 <= h*beta) by nra. nra. Qed.

(* The peak-side hypothesis (dp*d + r*beta <= 0), with dp = |P-O|, r the radius,
   pins the sign of the shorter combination pa*d + h*beta.  Proof: a squared
   comparison from |P-O| >= |(P-O).n| and r >= |d|, by sign cases. *)
Lemma need_bound :
  forall h d r pa beta dp : R,
    0 < h -> 0 < r -> 0 < dp -> 0 <= pa ->
    r*r = h*h + d*d -> dp*dp = pa*pa + beta*beta ->
    dp*d + r*beta <= 0 -> pa*d + h*beta <= 0.
Proof.
  intros h d r pa beta dp Hh Hr Hdp Hpa Hr2 Hdp2 H.
  assert (E1 : (dp*d)*(dp*d) = (pa*pa)*(d*d) + (beta*beta)*(d*d)).
  { replace ((dp*d)*(dp*d)) with ((dp*dp)*(d*d)) by ring. rewrite Hdp2. ring. }
  assert (E2 : (r*beta)*(r*beta) = (h*h)*(beta*beta) + (d*d)*(beta*beta)).
  { replace ((r*beta)*(r*beta)) with ((r*r)*(beta*beta)) by ring. rewrite Hr2. ring. }
  destruct (Rle_or_lt beta 0) as [Hb | Hb];
  destruct (Rle_or_lt d 0) as [Hd | Hd].
  - nra.
  - assert (Hfac : dp*d - r*beta >= 0) by nra.
    assert (Hsq0 : (dp*d)*(dp*d) <= (r*beta)*(r*beta)) by nra.
    assert (Hpasq : (pa*pa)*(d*d) <= (h*h)*(beta*beta)) by (rewrite E1, E2 in Hsq0; lra).
    apply (sq_to_lin_pos h d pa beta); assumption.
  - assert (Hfac : dp*d - r*beta <= 0) by nra.
    assert (Hsq0 : (r*beta)*(r*beta) <= (dp*d)*(dp*d)) by nra.
    assert (Hpasq : (h*h)*(beta*beta) <= (pa*pa)*(d*d)) by (rewrite E1, E2 in Hsq0; lra).
    apply (sq_to_lin_neg h d pa beta); assumption.
  - nra.
Qed.

(* Mirror sign of need_bound (peak on the other side of the chord). *)
Lemma need_bound2 :
  forall h d r pa beta dp : R,
    0 < h -> 0 < r -> 0 < dp -> 0 <= pa ->
    r*r = h*h + d*d -> dp*dp = pa*pa + beta*beta ->
    dp*d + r*beta >= 0 -> pa*d + h*beta >= 0.
Proof.
  intros h d r pa beta dp Hh Hr Hdp Hpa Hr2 Hdp2 H.
  assert (Hn : pa*(-d) + h*(-beta) <= 0).
  { apply (need_bound h (-d) r pa (-beta) dp); try assumption; try nra. }
  lra.
Qed.

(* Circle lies on one side of its tangent at E=(h,0): <E-O, X-E> <= 0. *)
Lemma tangent_E :
  forall h d r xa xb : R,
    r*r = h*h + d*d ->
    xa*xa + (xb-d)*(xb-d) = r*r ->
    h*(xa-h) - d*xb <= 0.
Proof. intros h d r xa xb Hr2 Hcirc. nra. Qed.

(* The scalar chord-frame core (endpoint E): with X on the far side of the chord
   from the radial foot and pa >= 0, the dot at X does not exceed the dot at E. *)
Lemma chord_caseE :
  forall h d r pa beta xa xb dp : R,
    0 < h -> 0 < r -> 0 < dp -> 0 <= pa ->
    r*r = h*h + d*d ->
    dp*dp = pa*pa + beta*beta ->
    xa*xa + (xb-d)*(xb-d) = r*r ->
    xb*(dp*d + r*beta) <= 0 ->
    pa*(xa-h) + beta*xb <= 0.
Proof.
  intros h d r pa beta xa xb dp Hh Hr Hdp Hpa Hr2 Hdp2 Hcirc Hside.
  assert (Htan : h*(xa-h) - d*xb <= 0) by (apply (tangent_E h d r xa xb); assumption).
  assert (Hkey : xb*(pa*d + h*beta) <= 0).
  { destruct (Rtotal_order xb 0) as [Hlt | [Heq | Hgt]].
    - assert (dp*d + r*beta >= 0) by nra.
      assert (pa*d + h*beta >= 0) by (apply (need_bound2 h d r pa beta dp); assumption).
      nra.
    - subst xb. lra.
    - assert (dp*d + r*beta <= 0) by nra.
      assert (pa*d + h*beta <= 0) by (apply (need_bound h d r pa beta dp); assumption).
      nra. }
  assert (Hcombine : h*(pa*(xa-h)+beta*xb)
                     = xb*(pa*d+h*beta) + pa*(h*(xa-h)-d*xb)) by ring.
  assert (pa*(h*(xa-h)-d*xb) <= 0) by nra.
  nra.
Qed.

(* §2b  The planar single-peak dot bound (headline, Qed).             *)
(* Reader's map: the proof sets up the L-scaled chord frame described in the   *)
(* CHORD-FRAME REDUCTION comment above (SE horizontal, so `side` is the         *)
(* perpendicular coordinate), discharges the bridge identities to the scalar    *)
(* hypotheses of the §2a core, then applies `chord_caseE` at endpoint E and its *)
(* S<->E reflection at endpoint S.                                              *)
Lemma arc_dot_max_at_endpoint : forall O P S E X r,
  dist O S = r -> dist O E = r -> dist O X = r ->
  side S E X * side S E (radial_foot O P r) <= 0 ->
  0 < dist O P ->
  0 < dist S E ->
  gdot O P X <= Rmax (gdot O P S) (gdot O P E).
Proof.
  intros O P S E X r HS HE HX Hside Hd HSE.
  set (ox := px O). set (oy := py O).
  set (ppx := px P). set (ppy := py P).
  set (sx := px S). set (sy := py S).
  set (ex := px E). set (ey := py E).
  set (xx := px X). set (xy := py X).
  set (ux := ex - sx). set (uy := ey - sy).
  set (m := ux*ux + uy*uy).
  (* m > 0 (S <> E) *)
  assert (Hm : 0 < m).
  { pose proof (dist_mul_self S E) as Hms.
    assert (Hpos : 0 < dist S E * dist S E) by nra.
    rewrite Hms in Hpos. unfold dist_sq in Hpos.
    unfold m, ux, uy, ex, sx, ey, sy. nra. }
  set (L := sqrt m).
  assert (HL : 0 < L) by (apply sqrt_lt_R0; exact Hm).
  assert (HLL : L*L = m) by (unfold L; rewrite sqrt_sqrt; lra).
  (* r > 0 *)
  assert (Hr : 0 < r).
  { destruct (Rlt_or_le 0 r) as [Hpos | Hle]; [exact Hpos | exfalso].
    pose proof (dist_nonneg O S) as Hn.
    assert (Hr0 : r = 0) by lra.
    assert (HdOS : dist O S = 0) by (rewrite HS; exact Hr0).
    assert (HdOE : dist O E = 0) by (rewrite HE; exact Hr0).
    apply dist_eq_zero_iff in HdOS. apply dist_eq_zero_iff in HdOE.
    assert (dist S E = 0).
    { apply dist_eq_zero_iff. destruct HdOS as [a1 a2]. destruct HdOE as [b1 b2].
      split; [ rewrite <- a1, <- b1 | rewrite <- a2, <- b2 ]; reflexivity. }
    lra. }
  set (dp := dist O P).
  assert (Hdp : 0 < dp) by exact Hd.
  assert (Hdpne : dp <> 0) by lra.
  assert (Hdp2 : dp*dp = (ppx-ox)*(ppx-ox)+(ppy-oy)*(ppy-oy)).
  { unfold dp. rewrite dist_mul_self. unfold dist_sq, ppx, ox, ppy, oy. ring. }
  assert (HrS : (ox-sx)*(ox-sx)+(oy-sy)*(oy-sy) = r*r).
  { pose proof (dist_mul_self O S) as H. rewrite HS in H.
    unfold dist_sq in H. unfold ox, sx, oy, sy. lra. }
  assert (HrE : (ox-ex)*(ox-ex)+(oy-ey)*(oy-ey) = r*r).
  { pose proof (dist_mul_self O E) as H. rewrite HE in H.
    unfold dist_sq in H. unfold ox, ex, oy, ey. lra. }
  assert (HrX : (ox-xx)*(ox-xx)+(oy-xy)*(oy-xy) = r*r).
  { pose proof (dist_mul_self O X) as H. rewrite HX in H.
    unfold dist_sq in H. unfold ox, xx, oy, xy. lra. }
  (* chord-frame scaled quantities (L-scaled; no square roots except R, DP) *)
  set (D := -(ox-sx)*uy + (oy-sy)*ux).
  set (Pt := (ppx-ox)*ux + (ppy-oy)*uy).
  set (Pn := -(ppx-ox)*uy + (ppy-oy)*ux).
  set (Xn := -(xx-sx)*uy + (xy-sy)*ux).
  set (H := m/2).
  set (R := L*r).
  set (DP := L*dp).
  set (Xt := (xx-ox)*ux + (xy-oy)*uy).
  assert (HH : 0 < H) by (unfold H; lra).
  assert (HR : 0 < R) by (unfold R; apply Rmult_lt_0_compat; assumption).
  assert (HDP : 0 < DP) by (unfold DP; apply Rmult_lt_0_compat; assumption).
  (* (O-S).U = m/2 (O on the perpendicular bisector of SE) *)
  assert (HdotSU : (ox-sx)*ux + (oy-sy)*uy = m/2).
  { assert (Heq : (ox-ex)*(ox-ex)+(oy-ey)*(oy-ey)
                  = (ox-sx)*(ox-sx)+(oy-sy)*(oy-sy)) by (rewrite HrE, HrS; ring).
    unfold m, ux, uy in *. lra. }
  (* Bridges to chord_caseE's hypotheses. *)
  assert (BR : R*R = H*H + D*D).
  { assert (HDsq : D*D = ((ox-sx)*(ox-sx)+(oy-sy)*(oy-sy))*m
                         - ((ox-sx)*ux+(oy-sy)*uy)*((ox-sx)*ux+(oy-sy)*uy))
      by (unfold D, m; ring).
    rewrite HrS, HdotSU in HDsq.
    assert (Hrr : R*R = m*(r*r)) by (unfold R; rewrite <- HLL; ring).
    unfold H. rewrite Hrr, HDsq. lra. }
  assert (BDP : DP*DP = Pt*Pt + Pn*Pn).
  { assert (Hd2 : DP*DP = m*(dp*dp)) by (unfold DP; rewrite <- HLL; ring).
    rewrite Hd2, Hdp2. unfold Pt, Pn, m, ux, uy. ring. }
  assert (BX : Xt*Xt + (Xn-D)*(Xn-D) = R*R).
  { assert (Hrr : R*R = m*(r*r)) by (unfold R; rewrite <- HLL; ring).
    rewrite Hrr, <- HrX.
    assert (HXn : Xn - D = -(xx-ox)*uy + (xy-oy)*ux) by (unfold Xn, D, ux, uy; ring).
    rewrite HXn. unfold Xt, m, ux, uy. ring. }
  (* side S E X = Xn ; side S E F = D + (r/dp)*Pn *)
  assert (HsX : side S E X = Xn) by (unfold side, Xn, ux, uy, ex, sx, ey, sy, xx, xy; ring).
  assert (Hne : dist O P <> 0) by (unfold dp in Hdpne; exact Hdpne).
  assert (HsF : side S E (radial_foot O P r) = D + (r/dp)*Pn).
  { unfold side, radial_foot, D, Pn, dp, ux, uy, ox, oy, ppx, ppy, ex, ey, sx, sy.
    cbn [px py]. field. exact Hne. }
  assert (BSide : Xn*(DP*D + R*Pn) <= 0).
  { rewrite HsX, HsF in Hside.
    assert (Heq : Xn*(DP*D + R*Pn) = (L*dp)*(Xn*(D + (r/dp)*Pn))).
    { unfold DP, R. field. exact Hdpne. }
    rewrite Heq.
    assert (0 < L*dp) by (apply Rmult_lt_0_compat; assumption).
    nra. }
  (* conclusion identities: m*(gX - gE) = Pt*(Xt-H)+Pn*Xn, similarly for S. *)
  assert (LagIE : m*(gdot O P X - gdot O P E)
        = Pt*((xx-ex)*ux+(xy-ey)*uy) + Pn*(-(xx-ex)*uy+(xy-ey)*ux)).
  { unfold gdot, Pt, Pn, m, ux, uy, ox, oy, ppx, ppy, ex, ey, xx, xy, sx, sy. ring. }
  assert (HEOU : (ex-ox)*ux+(ey-oy)*uy = m/2).
  { assert (Ht : (ex-ox)*ux+(ey-oy)*uy = m - ((ox-sx)*ux+(oy-sy)*uy))
      by (unfold m, ux, uy; ring).
    rewrite HdotSU in Ht. lra. }
  assert (HXEt : (xx-ex)*ux+(xy-ey)*uy = Xt - H).
  { assert (Ht : (xx-ex)*ux+(xy-ey)*uy
          = ((xx-ox)*ux+(xy-oy)*uy) - ((ex-ox)*ux+(ey-oy)*uy)) by (unfold ux, uy; ring).
    rewrite HEOU in Ht. unfold Xt, H. lra. }
  assert (HXEn : -(xx-ex)*uy+(xy-ey)*ux = Xn) by (unfold Xn, ux, uy; ring).
  assert (IE : m*(gdot O P X - gdot O P E) = Pt*(Xt-H) + Pn*Xn).
  { rewrite LagIE, HXEt, HXEn. reflexivity. }
  assert (LagIS : m*(gdot O P X - gdot O P S)
        = Pt*((xx-sx)*ux+(xy-sy)*uy) + Pn*(-(xx-sx)*uy+(xy-sy)*ux)).
  { unfold gdot, Pt, Pn, m, ux, uy, ox, oy, ppx, ppy, ex, ey, xx, xy, sx, sy. ring. }
  assert (HXSt : (xx-sx)*ux+(xy-sy)*uy = Xt + H).
  { assert (Ht : (xx-sx)*ux+(xy-sy)*uy
          = ((xx-ox)*ux+(xy-oy)*uy) + ((ox-sx)*ux+(oy-sy)*uy)) by (unfold ux, uy; ring).
    rewrite HdotSU in Ht. unfold Xt, H. lra. }
  assert (IS : m*(gdot O P X - gdot O P S) = Pt*(Xt+H) + Pn*Xn).
  { rewrite LagIS, HXSt. unfold Xn. reflexivity. }
  (* Case split on the sign of Pt = (P-O).(E-S). *)
  destruct (Rle_or_lt 0 Pt) as [HPt | HPt].
  - (* Pt >= 0: chord_caseE gives gX <= gE <= Rmax. *)
    assert (HconE : Pt*(Xt-H) + Pn*Xn <= 0)
      by (apply (chord_caseE H D R Pt Pn Xt Xn DP); assumption).
    assert (gdot O P X <= gdot O P E) by nra.
    apply Rle_trans with (gdot O P E); [assumption | apply Rmax_r].
  - (* Pt < 0: reflect the chord frame (S <-> E) to get gX <= gS <= Rmax. *)
    assert (HDP2' : DP*DP = (-Pt)*(-Pt) + Pn*Pn) by (rewrite BDP; ring).
    assert (Hcirc' : (-Xt)*(-Xt) + (Xn-D)*(Xn-D) = R*R) by (rewrite <- BX; ring).
    assert (HconS : (-Pt)*((-Xt)-H) + Pn*Xn <= 0).
    { apply (chord_caseE H D R (-Pt) Pn (-Xt) Xn DP);
        [ exact HH | exact HR | exact HDP | lra | exact BR
        | exact HDP2' | exact Hcirc' | exact BSide ]. }
    assert (Pt*(Xt+H) + Pn*Xn <= 0) by nra.
    assert (gdot O P X <= gdot O P S) by nra.
    apply Rle_trans with (gdot O P S); [assumption | apply Rmax_l].
Qed.
