(* QedRootsRefute.v -- qedroots, refutation side: exact certificates that a
   polynomial is NOT hyperbolic, from rational coefficient enclosures.

   Layer `qedroots` of the qed chain
       qedinterval -> qedpoly -> qedroots -> qedanalytic -> qedjensen.

   Why: `box_cert` failing proves nothing (QedRoots: sound, incomplete).
   The Davenport-Heilbronn control (QEX-2B) needs a positive, exact
   statement "this Jensen polynomial is not hyperbolic".  This file
   supplies one.

   Laguerre inequality.  If p = c * prod (X - r_i) (multiset), then for
   every real x
       L_p(x) := p'(x)^2 - p(x) p''(x) >= 0.            (laguerre_hyperbolic)
   Proof is algebraic: for f = (X - r) g,
       L_f = g^2 + (X - r)^2 L_g.
   So one rational point x with L_p(x) < 0 refutes hyperbolicity.

   Certificates (boolean over Q, vm_compute):
     lag_box_cert b x   interval upper bound of D^2 - P*E < 0, where P, D, E
                        are the exact enclosures of p, p', p'' at x over b.
                        Sound: in_box p b -> lag_box_cert b x = true
                               -> ~ hyperbolic p          (lag_box_cert_sound)
   Robust: an open condition, so it survives small coefficient boxes.

   Strength: complete in degree 2 -- at x = -b/(2c) the Laguerre form is
   (b^2 - 4ac)/2 (laguerre_quadratic_vertex), i.e. the Turan inequality for
   degree-2 Jensen polynomials.  Not claimed complete in higher degree.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals QArith Qreals Lra Psatz List.
From NTS.Proofs Require Import QedPoly QedInterval QedRoots.
Import ListNotations.

Local Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* Derivatives of linear products.                                      *)
(* ------------------------------------------------------------------ *)

Fixpoint dprod (rs : list R) (x : R) : R :=
  match rs with
  | [] => 0
  | r :: t => prodlin t x + (x - r) * dprod t x
  end.

Fixpoint ddprod (rs : list R) (x : R) : R :=
  match rs with
  | [] => 0
  | r :: t => 2 * dprod t x + (x - r) * ddprod t x
  end.

Lemma prodlin_derivable rs x : derivable_pt_lim (prodlin rs) x (dprod rs x).
Proof.
  revert x; induction rs as [|r t IH]; intros x; simpl.
  - apply derivable_pt_lim_const.
  - replace (prodlin t x + (x - r) * dprod t x)
      with ((1 - 0) * prodlin t x + (x - r) * dprod t x) by ring.
    apply (derivable_pt_lim_mult (fun y => y - r) (prodlin t)); [|apply IH].
    apply (derivable_pt_lim_minus (fun y => y) (fun _ => r));
      [apply derivable_pt_lim_id|apply derivable_pt_lim_const].
Qed.

Lemma dprod_derivable rs x : derivable_pt_lim (dprod rs) x (ddprod rs x).
Proof.
  revert x; induction rs as [|r t IH]; intros x; simpl.
  - apply derivable_pt_lim_const.
  - replace (2 * dprod t x + (x - r) * ddprod t x)
      with (dprod t x + ((1 - 0) * dprod t x + (x - r) * ddprod t x)) by ring.
    apply (derivable_pt_lim_plus (prodlin t) (fun y => (y - r) * dprod t y));
      [apply prodlin_derivable|].
    apply (derivable_pt_lim_mult (fun y => y - r) (dprod t)); [|apply IH].
    apply (derivable_pt_lim_minus (fun y => y) (fun _ => r));
      [apply derivable_pt_lim_id|apply derivable_pt_lim_const].
Qed.

(* The algebraic heart:  L_{(X-r) g} = g^2 + (X-r)^2 L_g. *)
Lemma laguerre_prodlin rs x :
  0 <= dprod rs x * dprod rs x - prodlin rs x * ddprod rs x.
Proof.
  induction rs as [|r t IH]; simpl; [lra|].
  replace ((prodlin t x + (x - r) * dprod t x) *
           (prodlin t x + (x - r) * dprod t x) -
           (x - r) * prodlin t x * (2 * dprod t x + (x - r) * ddprod t x))
    with (prodlin t x * prodlin t x +
          (x - r) * (x - r) *
          (dprod t x * dprod t x - prodlin t x * ddprod t x)) by ring.
  pose proof (Rle_0_sqr (prodlin t x)). pose proof (Rle_0_sqr (x - r)).
  unfold Rsqr in *. nra.
Qed.

Definition laguerre (p : list R) (x : R) : R :=
  peval (pderiv p) x * peval (pderiv p) x -
  peval p x * peval (pderiv (pderiv p)) x.

Theorem laguerre_hyperbolic p : hyperbolic p -> forall x, 0 <= laguerre p x.
Proof.
  intros (c & rs & _ & _ & Hf) x.
  assert (H1 : forall y, peval (pderiv p) y = c * dprod rs y).
  { intros y. apply (uniqueness_limite (peval p) y).
    - apply peval_derivable.
    - apply (derivable_pt_lim_ext (fun z => c * prodlin rs z)).
      + intros z. now rewrite Hf.
      + apply derivable_pt_lim_scal, prodlin_derivable. }
  assert (H2 : peval (pderiv (pderiv p)) x = c * ddprod rs x).
  { apply (uniqueness_limite (peval (pderiv p)) x).
    - apply peval_derivable.
    - apply (derivable_pt_lim_ext (fun z => c * dprod rs z)).
      + intros z. now rewrite H1.
      + apply derivable_pt_lim_scal, dprod_derivable. }
  unfold laguerre. rewrite H1, H2, Hf.
  pose proof (laguerre_prodlin rs x). pose proof (Rle_0_sqr c).
  unfold Rsqr in *.
  replace (c * dprod rs x * (c * dprod rs x) -
           c * prodlin rs x * (c * ddprod rs x))
    with ((c * c) * (dprod rs x * dprod rs x - prodlin rs x * ddprod rs x))
    by ring.
  apply Rmult_le_pos; assumption.
Qed.

(* Degree 2: the Laguerre form at the vertex is half the discriminant. *)
Lemma laguerre_quadratic_vertex a b c :
  c <> 0 -> laguerre [a; b; c] (- b / (2 * c)) = (b * b - 4 * a * c) / 2.
Proof.
  intros Hc. unfold laguerre, pderiv. simpl. field. exact Hc.
Qed.

Corollary quadratic_negative_discriminant_not_hyperbolic a b c :
  c <> 0 -> b * b - 4 * a * c < 0 -> ~ hyperbolic [a; b; c].
Proof.
  intros Hc Hd Hh. pose proof (laguerre_hyperbolic _ Hh (- b / (2 * c))) as H.
  rewrite laguerre_quadratic_vertex in H by exact Hc. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Interval bounds for D^2 and P*E.                                     *)
(* ------------------------------------------------------------------ *)

Lemma sq_upper dl dh d :
  dl <= d <= dh -> d * d <= dl * dl \/ d * d <= dh * dh.
Proof. intros H. destruct (Rle_dec 0 d); [right|left]; nra. Qed.

Lemma mul_lower pl ph el eh p e :
  pl <= p <= ph -> el <= e <= eh ->
  pl * el <= p * e \/ pl * eh <= p * e \/ ph * el <= p * e \/ ph * eh <= p * e.
Proof.
  intros Hp He.
  assert (Hpe : pl * e <= p * e \/ ph * e <= p * e).
  { destruct (Rle_dec 0 e); [left|right]; nra. }
  destruct Hpe as [Hpe|Hpe].
  - destruct (Rle_dec 0 pl); [left|right; left]; nra.
  - destruct (Rle_dec 0 ph); [right; right; left|right; right; right]; nra.
Qed.

Local Open Scope Q_scope.

Definition qmax (a b : Q) : Q := if Qle_bool a b then b else a.
Definition qmin (a b : Q) : Q := if Qle_bool a b then a else b.

Definition lag_upper (b : box) (x : Q) : Q :=
  let (pl, ph) := ieval b x in
  let (dl, dh) := ieval (pderivB b) x in
  let (el, eh) := ieval (pderivB (pderivB b)) x in
  qmax (dl * dl) (dh * dh) -
  qmin (qmin (pl * el) (pl * eh)) (qmin (ph * el) (ph * eh)).

Definition lag_box_cert (b : box) (x : Q) : bool := Qltb (lag_upper b x) 0.

Local Open Scope R_scope.

Lemma qmax_ge a b : Q2R a <= Q2R (qmax a b) /\ Q2R b <= Q2R (qmax a b).
Proof.
  unfold qmax. destruct (Qle_bool a b) eqn:E.
  - apply Qle_bool_iff, Qle_Rle in E. lra.
  - split; [lra|]. apply Rlt_le, Qlt_Rlt, Qnot_le_lt.
    intros H; apply Qle_bool_iff in H; congruence.
Qed.

Lemma qmin_le a b : Q2R (qmin a b) <= Q2R a /\ Q2R (qmin a b) <= Q2R b.
Proof.
  unfold qmin. destruct (Qle_bool a b) eqn:E.
  - apply Qle_bool_iff, Qle_Rle in E. lra.
  - split; [|lra]. apply Rlt_le, Qlt_Rlt, Qnot_le_lt.
    intros H; apply Qle_bool_iff in H; congruence.
Qed.

Theorem lag_upper_sound p b x :
  in_box p b -> laguerre p (Q2R x) <= Q2R (lag_upper b x).
Proof.
  intros Hb.
  pose proof (ieval_sound _ _ x Hb) as HP.
  pose proof (ieval_sound _ _ x (in_box_pderiv _ _ Hb)) as HD.
  pose proof (ieval_sound _ _ x (in_box_pderiv _ _ (in_box_pderiv _ _ Hb))) as HE.
  unfold lag_upper, laguerre.
  destruct (ieval b x) as [pl ph].
  destruct (ieval (pderivB b) x) as [dl dh].
  destruct (ieval (pderivB (pderivB b)) x) as [el eh].
  simpl in HP, HD, HE. cbv beta iota.
  rewrite Q2R_minus.
  pose proof (qmax_ge (dl * dl) (dh * dh)) as Mx.
  pose proof (qmin_le (pl * el) (pl * eh)) as M1.
  pose proof (qmin_le (ph * el) (ph * eh)) as M2.
  pose proof (qmin_le (qmin (pl * el) (pl * eh)) (qmin (ph * el) (ph * eh))) as M3.
  rewrite !Q2R_mult in Mx, M1, M2.
  set (D := peval (pderiv p) (Q2R x)) in *.
  set (P := peval p (Q2R x)) in *.
  set (E := peval (pderiv (pderiv p)) (Q2R x)) in *.
  destruct (sq_upper _ _ D HD) as [Hd|Hd];
  destruct (mul_lower _ _ _ _ P E HP HE) as [Hm|[Hm|[Hm|Hm]]]; lra.
Qed.

(* REFUTATION BRIDGE: a passed Laguerre certificate shows that NO real
   coefficient vector inside the box is hyperbolic. *)
Theorem lag_box_cert_sound p b x :
  in_box p b -> lag_box_cert b x = true -> ~ hyperbolic p.
Proof.
  intros Hb Hc Hh.
  pose proof (laguerre_hyperbolic p Hh (Q2R x)) as H0.
  pose proof (lag_upper_sound p b x Hb) as H1.
  apply Qltb_spec in Hc. rewrite Q2R_0 in Hc. lra.
Qed.

Corollary lag_point_cert_sound (p : list Q) x :
  lag_box_cert (point_box p) x = true -> ~ hyperbolic (pQ2R p).
Proof. intros H. exact (lag_box_cert_sound _ _ _ (in_point_box p) H). Qed.

(* The two certificate kinds never both pass on overlapping data. *)
Corollary box_cert_lag_exclusive p b1 b2 xs x :
  in_box p b1 -> in_box p b2 ->
  box_cert b1 xs = true -> lag_box_cert b2 x = false.
Proof.
  intros H1 H2 Hc. destruct (lag_box_cert b2 x) eqn:E; [|reflexivity].
  exfalso. apply (lag_box_cert_sound p b2 x H2 E).
  exact (cert_hyperbolic p b1 xs H1 Hc).
Qed.
