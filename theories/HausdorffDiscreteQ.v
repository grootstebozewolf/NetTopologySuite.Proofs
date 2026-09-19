(* ============================================================================
   NetTopologySuite.Proofs.HausdorffDiscreteQ
   ----------------------------------------------------------------------------
   #423 ticket-10 line 2: the EXTRACTABLE rational twin of HausdorffDensify's
   directed discrete Hausdorff value, and its agreement theorem
   (claimId 423-t10-oracle).

   The oracle keywords HAUSDORFF_DIRECTED / HAUSDORFF_SYMM (ADR-0006 adapters
   on the Oracle line protocol; oracle/driver.ml) emit JTS
   DiscreteHausdorffDistance's h: vertices of A against the whole geometry B,
   unsquared.  The reference behind the wire is this file:

     q_ddh_sq A B     : Q   -- exact squared directed value, computed on Q
                             with the same clamped point-to-segment kernel
                             as LECSegmentRow.seg_dist (Qmax 0 (Qmin 1 t)),
                             the same min-over-edges / max-over-vertices folds
                             as HausdorffDensify, then Qred.
     q_hsymm_sq A B   : Q   -- max of the two directions.

   Agreement (3-axiom Reals):
     Q2R (q_ddh_sq A B)   = (directed_discrete_h (map qpt_R A) (map qpt_R B))^2
     sqrt (Q2R (q_ddh_sq A B)) = directed_discrete_h (map qpt_R A) (map qpt_R B)
   and the symmetric twins.  The driver prints sqrt of the extracted rational
   (the only float step; the exact rational is printed beside it as the
   companion token), so the wire value is JTS's unsquared h rounded once past
   certified rational algebra -- the allowlist's INTERFACE-BOUNDARY shape.

   Locked JTS pair: q_ddh_sq A B == 500 exactly (HausdorffDensify.
   jts_discrete_value: directed_discrete_h = sqrt 500).  The locus value
   directed_locus_h is NOT extracted and is not what DiscreteHausdorffDistance
   returns; nothing here computes it.

   Not: 423-a / 423-b remint (those are vertex-to-vertex); no
   Linearise.hausdorff_le; no NTS/GEOS port; no first_cook_scope.

   WITNESS topic: metric · claimId: 423-t10-oracle · witness: 423-t10-oracle
   Q part 0-axiom; agreement 3-axiom (Stdlib Reals).
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List QArith Qminmax Qreals.
From NTS.Proofs Require Import Distance Overlay LECSegmentRow HausdorffDensify
  CircularCookLineArcZ CircularCookLineArcR.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  The rational kernel (extractable).                                     *)
(* -------------------------------------------------------------------------- *)

Local Open Scope Q_scope.

Definition qdist_sq (p q : QPt) : Q :=
  (qx p - qx q) * (qx p - qx q) + (qy p - qy q) * (qy p - qy q).

Definition qseg_point (a b : QPt) (t : Q) : QPt :=
  mkQPt (qx a + t * (qx b - qx a)) (qy a + t * (qy b - qy a)).

Definition qseg_dot (a b p : QPt) : Q :=
  (qx p - qx a) * (qx b - qx a) + (qy p - qy a) * (qy b - qy a).

(* Clamped parameter; degenerate segment takes 0 (LECSegmentRow.seg_t twin). *)
Definition qseg_t (a b p : QPt) : Q :=
  if Qeq_bool (qdist_sq a b) 0 then 0
  else Qmax 0 (Qmin 1 (qseg_dot a b p / qdist_sq a b)).

Definition qseg_dist_sq (a b p : QPt) : Q :=
  qdist_sq p (qseg_point a b (qseg_t a b p)).

Fixpoint qedges (l : list QPt) : list (QPt * QPt) :=
  match l with
  | a :: ((b :: _) as l') => (a, b) :: qedges l'
  | _ => []
  end.

Fixpoint qdist_to_edges (p : QPt) (es : list (QPt * QPt)) : Q :=
  match es with
  | [] => 0
  | [e] => qseg_dist_sq (fst e) (snd e) p
  | e :: es' => Qmin (qseg_dist_sq (fst e) (snd e) p) (qdist_to_edges p es')
  end.

Definition qdist_to_polyline (p : QPt) (B : list QPt) : Q :=
  qdist_to_edges p (qedges B).

Fixpoint qlist_max (f : QPt -> Q) (l : list QPt) : Q :=
  match l with
  | [] => 0
  | [x] => f x
  | x :: l' => Qmax (f x) (qlist_max f l')
  end.

Definition q_ddh_sq_raw (A B : list QPt) : Q :=
  qlist_max (fun a => qdist_to_polyline a B) A.

(* HAUSDORFF_DIRECTED: exact squared value, reduced. *)
Definition q_ddh_sq (A B : list QPt) : Q := Qred (q_ddh_sq_raw A B).

(* HAUSDORFF_SYMM: max of the two directions, reduced. *)
Definition q_hsymm_sq (A B : list QPt) : Q :=
  Qred (Qmax (q_ddh_sq_raw A B) (q_ddh_sq_raw B A)).

Local Close Scope Q_scope.

(* -------------------------------------------------------------------------- *)
(* §2  Q2R transport for min / max / division.                                *)
(* -------------------------------------------------------------------------- *)

Local Open Scope R_scope.

Ltac q2r :=
  repeat first [ rewrite Q2R_plus | rewrite Q2R_minus | rewrite Q2R_mult
               | rewrite RMicromega.Q2R_0 | rewrite RMicromega.Q2R_1 ].

Lemma Q2R_qmax : forall x y : Q, Q2R (Qmax x y) = Rmax (Q2R x) (Q2R y).
Proof.
  intros x y.
  destruct (Q.max_spec x y) as [[Hlt Heq] | [Hle Heq]].
  - rewrite (Qeq_eqR _ _ Heq). rewrite Rmax_right; [ reflexivity | ].
    apply Rlt_le. apply Qlt_Rlt. exact Hlt.
  - rewrite (Qeq_eqR _ _ Heq). rewrite Rmax_left; [ reflexivity | ].
    apply Qle_Rle. exact Hle.
Qed.

Lemma Q2R_qmin : forall x y : Q, Q2R (Qmin x y) = Rmin (Q2R x) (Q2R y).
Proof.
  intros x y.
  destruct (Q.min_spec x y) as [[Hlt Heq] | [Hle Heq]].
  - rewrite (Qeq_eqR _ _ Heq). rewrite Rmin_left; [ reflexivity | ].
    apply Rlt_le. apply Qlt_Rlt. exact Hlt.
  - rewrite (Qeq_eqR _ _ Heq). rewrite Rmin_right; [ reflexivity | ].
    apply Qle_Rle. exact Hle.
Qed.

Lemma qdist_sq_R : forall p q : QPt,
  Q2R (qdist_sq p q) = dist_sq (qpt_R p) (qpt_R q).
Proof. intros p q. unfold qdist_sq, dist_sq, qpt_R. cbn [px py]. q2r. reflexivity. Qed.

Lemma qseg_dot_R : forall a b p : QPt,
  Q2R (qseg_dot a b p) = seg_dot (qpt_R a) (qpt_R b) (qpt_R p).
Proof. intros a b p. unfold qseg_dot, seg_dot, qpt_R. cbn [px py]. q2r. reflexivity. Qed.

Lemma qseg_point_R : forall (a b : QPt) (t : Q),
  qpt_R (qseg_point a b t) = seg_point (qpt_R a) (qpt_R b) (Q2R t).
Proof.
  intros a b t. unfold qseg_point, seg_point, qpt_R. cbn [px py qx qy].
  q2r. reflexivity.
Qed.

Lemma qseg_t_R : forall a b p : QPt,
  Q2R (qseg_t a b p) = seg_t (qpt_R a) (qpt_R b) (qpt_R p).
Proof.
  intros a b p. unfold qseg_t, seg_t.
  rewrite <- qdist_sq_R.
  destruct (Qeq_bool (qdist_sq a b) 0) eqn:E;
    destruct (Req_EM_T (Q2R (qdist_sq a b)) 0) as [Hz | Hnz].
  - apply RMicromega.Q2R_0.
  - exfalso. apply Hnz. apply Qeq_bool_iff in E.
    rewrite (Qeq_eqR _ _ E). apply RMicromega.Q2R_0.
  - exfalso.
    assert (Hq : (qdist_sq a b == 0)%Q).
    { apply eqR_Qeq. rewrite Hz. symmetry. apply RMicromega.Q2R_0. }
    apply Qeq_bool_iff in Hq. rewrite Hq in E. discriminate.
  - assert (Hne : ~ (qdist_sq a b == 0)%Q).
    { intro Hq. apply Qeq_bool_iff in Hq. rewrite Hq in E. discriminate. }
    rewrite Q2R_qmax, Q2R_qmin, Q2R_div by exact Hne.
    rewrite qseg_dot_R, RMicromega.Q2R_0, RMicromega.Q2R_1. reflexivity.
Qed.

Lemma qseg_dist_sq_R : forall a b p : QPt,
  Q2R (qseg_dist_sq a b p) =
  seg_dist (qpt_R a) (qpt_R b) (qpt_R p) * seg_dist (qpt_R a) (qpt_R b) (qpt_R p).
Proof.
  intros a b p. unfold qseg_dist_sq, seg_dist, dist.
  rewrite sqrt_sqrt by apply dist_sq_nonneg.
  rewrite qdist_sq_R, qseg_point_R, qseg_t_R. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Squares commute with min / max on nonnegatives; folds transport.       *)
(* -------------------------------------------------------------------------- *)

Lemma Rmin_sq : forall x y, 0 <= x -> 0 <= y -> Rmin x y * Rmin x y = Rmin (x * x) (y * y).
Proof.
  intros x y Hx Hy.
  destruct (Rle_dec x y) as [Hle | Hgt].
  - rewrite (Rmin_left x y Hle). rewrite Rmin_left; [ reflexivity | nra ].
  - rewrite (Rmin_right x y) by lra. rewrite Rmin_right; [ reflexivity | nra ].
Qed.

Lemma Rmax_sq : forall x y, 0 <= x -> 0 <= y -> Rmax x y * Rmax x y = Rmax (x * x) (y * y).
Proof.
  intros x y Hx Hy.
  destruct (Rle_dec x y) as [Hle | Hgt].
  - rewrite (Rmax_right x y Hle). rewrite Rmax_right; [ reflexivity | nra ].
  - rewrite (Rmax_left x y) by lra. rewrite Rmax_left; [ reflexivity | nra ].
Qed.

Definition edge_R (e : QPt * QPt) : Edge := (qpt_R (fst e), qpt_R (snd e)).

Lemma qedges_R : forall l : list QPt,
  ring_edges (map qpt_R l) = map edge_R (qedges l).
Proof.
  induction l as [| a l' IH]; [ reflexivity | ].
  destruct l' as [| b l''].
  - reflexivity.
  - change (ring_edges (map qpt_R (a :: b :: l'')))
      with ((qpt_R a, qpt_R b) :: ring_edges (map qpt_R (b :: l''))).
    change (qedges (a :: b :: l'')) with ((a, b) :: qedges (b :: l'')).
    rewrite IH. reflexivity.
Qed.

Lemma qdist_to_edges_R : forall (p : QPt) (es : list (QPt * QPt)),
  Q2R (qdist_to_edges p es) =
  dist_to_edges (qpt_R p) (map edge_R es) * dist_to_edges (qpt_R p) (map edge_R es).
Proof.
  intros p es. induction es as [| e0 es' IH].
  - cbn. rewrite RMicromega.Q2R_0. ring.
  - destruct es' as [| e1 es''].
    + cbn [qdist_to_edges map dist_to_edges edge_R fst snd]. apply qseg_dist_sq_R.
    + change (qdist_to_edges p (e0 :: e1 :: es''))
        with (Qmin (qseg_dist_sq (fst e0) (snd e0) p) (qdist_to_edges p (e1 :: es''))).
      change (map edge_R (e0 :: e1 :: es'')) with (edge_R e0 :: map edge_R (e1 :: es'')).
      change (dist_to_edges (qpt_R p) (edge_R e0 :: map edge_R (e1 :: es'')))
        with (Rmin (seg_dist (fst (edge_R e0)) (snd (edge_R e0)) (qpt_R p))
                   (dist_to_edges (qpt_R p) (map edge_R (e1 :: es'')))).
      rewrite Q2R_qmin, qseg_dist_sq_R, IH.
      unfold edge_R. cbn [fst snd].
      rewrite Rmin_sq; [ reflexivity | apply dist_nonneg | apply dist_to_edges_nonneg ].
Qed.

Lemma qdist_to_polyline_R : forall (p : QPt) (B : list QPt),
  Q2R (qdist_to_polyline p B) =
  dist_to_polyline (qpt_R p) (map qpt_R B) * dist_to_polyline (qpt_R p) (map qpt_R B).
Proof.
  intros p B. unfold qdist_to_polyline, dist_to_polyline.
  rewrite qedges_R. apply qdist_to_edges_R.
Qed.

Lemma list_max_nonneg : forall {X : Type} (f : X -> R) (l : list X),
  (forall x, In x l -> 0 <= f x) -> 0 <= list_max f l.
Proof.
  intros X f l. induction l as [| y l' IH]; intros H.
  - cbn. lra.
  - destruct l' as [| z l''].
    + cbn. apply H. left. reflexivity.
    + change (list_max f (y :: z :: l'')) with (Rmax (f y) (list_max f (z :: l''))).
      apply Rmax_Rle. left. apply H. left. reflexivity.
Qed.

Lemma dist_to_polyline_nonneg : forall p B, 0 <= dist_to_polyline p B.
Proof. intros. apply dist_to_edges_nonneg. Qed.

Lemma directed_discrete_h_nonneg : forall A B, 0 <= directed_discrete_h A B.
Proof.
  intros A B. unfold directed_discrete_h. apply list_max_nonneg.
  intros a _. apply dist_to_polyline_nonneg.
Qed.

Lemma q_ddh_sq_raw_R : forall A B : list QPt,
  Q2R (q_ddh_sq_raw A B) =
  directed_discrete_h (map qpt_R A) (map qpt_R B) * directed_discrete_h (map qpt_R A) (map qpt_R B).
Proof.
  intros A B. unfold q_ddh_sq_raw, directed_discrete_h.
  induction A as [| a A' IH].
  - cbn. rewrite RMicromega.Q2R_0. ring.
  - destruct A' as [| a1 A''].
    + cbn [qlist_max map list_max]. apply qdist_to_polyline_R.
    + change (qlist_max (fun a0 => qdist_to_polyline a0 B) (a :: a1 :: A''))
        with (Qmax (qdist_to_polyline a B) (qlist_max (fun a0 => qdist_to_polyline a0 B) (a1 :: A''))).
      change (map qpt_R (a :: a1 :: A'')) with (qpt_R a :: map qpt_R (a1 :: A'')).
      change (list_max (fun a0 => dist_to_polyline a0 (map qpt_R B)) (qpt_R a :: map qpt_R (a1 :: A'')))
        with (Rmax (dist_to_polyline (qpt_R a) (map qpt_R B))
                   (list_max (fun a0 => dist_to_polyline a0 (map qpt_R B)) (map qpt_R (a1 :: A'')))).
      rewrite Q2R_qmax, qdist_to_polyline_R, IH.
      rewrite Rmax_sq; [ reflexivity | apply dist_to_polyline_nonneg | ].
      apply list_max_nonneg. intros x _. apply dist_to_polyline_nonneg.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Agreement theorems: the extracted rational is the proven value squared. *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"423-t10-oracle","topic":"metric","lemma":"q_ddh_sq_R","title":"HAUSDORFF_DIRECTED reference: Q2R of the extracted exact rational q_ddh_sq A B equals the square of HausdorffDensify.directed_discrete_h on the Q2R points","file":"theories/HausdorffDiscreteQ.v","witness":"423-t10-oracle"} *)
Theorem q_ddh_sq_R : forall A B : list QPt,
  Q2R (q_ddh_sq A B) =
  directed_discrete_h (map qpt_R A) (map qpt_R B) * directed_discrete_h (map qpt_R A) (map qpt_R B).
Proof.
  intros A B. unfold q_ddh_sq.
  rewrite (Qeq_eqR _ _ (Qred_correct (q_ddh_sq_raw A B))).
  apply q_ddh_sq_raw_R.
Qed.

Theorem sqrt_q_ddh_sq : forall A B : list QPt,
  sqrt (Q2R (q_ddh_sq A B)) = directed_discrete_h (map qpt_R A) (map qpt_R B).
Proof.
  intros A B. rewrite q_ddh_sq_R. apply sqrt_square. apply directed_discrete_h_nonneg.
Qed.

(* WITNESS {"claimId":"423-t10-oracle","topic":"metric","lemma":"q_hsymm_sq_R","title":"HAUSDORFF_SYMM reference: Q2R of the extracted q_hsymm_sq A B equals the square of the max of the two directed discrete values","file":"theories/HausdorffDiscreteQ.v","witness":"423-t10-oracle"} *)
Theorem q_hsymm_sq_R : forall A B : list QPt,
  Q2R (q_hsymm_sq A B) =
  Rmax (directed_discrete_h (map qpt_R A) (map qpt_R B))
       (directed_discrete_h (map qpt_R B) (map qpt_R A)) *
  Rmax (directed_discrete_h (map qpt_R A) (map qpt_R B))
       (directed_discrete_h (map qpt_R B) (map qpt_R A)).
Proof.
  intros A B. unfold q_hsymm_sq.
  rewrite (Qeq_eqR _ _ (Qred_correct _)).
  rewrite Q2R_qmax, !q_ddh_sq_raw_R.
  rewrite Rmax_sq; [ reflexivity | apply directed_discrete_h_nonneg | apply directed_discrete_h_nonneg ].
Qed.

Theorem sqrt_q_hsymm_sq : forall A B : list QPt,
  sqrt (Q2R (q_hsymm_sq A B)) =
  Rmax (directed_discrete_h (map qpt_R A) (map qpt_R B))
       (directed_discrete_h (map qpt_R B) (map qpt_R A)).
Proof.
  intros A B. rewrite q_hsymm_sq_R. apply sqrt_square.
  apply Rmax_Rle. left. apply directed_discrete_h_nonneg.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Locked JTS pair on Q: exactly 500.                                      *)
(* -------------------------------------------------------------------------- *)

Definition jts_qA : list QPt := [mkQPt 0 0; mkQPt 100 0; mkQPt 10 100].
Definition jts_qB : list QPt := [mkQPt 0 100; mkQPt 0 10; mkQPt 80 10].

(* WITNESS {"claimId":"423-t10-oracle","topic":"metric","lemma":"jts_q_ddh_sq_500","title":"locked JTS pair on Q: q_ddh_sq A B computes to exactly 500, the square of HausdorffDensify.jts_discrete_value's sqrt 500","file":"theories/HausdorffDiscreteQ.v","witness":"423-t10-oracle"} *)
Lemma jts_q_ddh_sq_500 : q_ddh_sq jts_qA jts_qB = 500%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma jts_q_hsymm_sq_value : (q_hsymm_sq jts_qA jts_qB == q_hsymm_sq jts_qB jts_qA)%Q.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Ticket stop.                                                           *)
(* -------------------------------------------------------------------------- *)

Inductive HausdorffOraclePark : Type :=
| HausdorffOracleKeyword.

Definition hausdorff_oracle_park_inhabits (c : HausdorffOraclePark) : Prop :=
  match c with
  | HausdorffOracleKeyword =>
      (* the two adapters exist on the Oracle line (oracle/driver.ml,
         HAUSDORFF_DIRECTED / HAUSDORFF_SYMM) and print sqrt of exactly these
         extracted rationals; the Rocq side of that keyword is this file. *)
      (forall A B : list QPt,
         sqrt (Q2R (q_ddh_sq A B)) = directed_discrete_h (map qpt_R A) (map qpt_R B))
      /\ (forall A B : list QPt,
            sqrt (Q2R (q_hsymm_sq A B)) =
            Rmax (directed_discrete_h (map qpt_R A) (map qpt_R B))
                 (directed_discrete_h (map qpt_R B) (map qpt_R A)))
  end.

(* WITNESS {"claimId":"423-t10-oracle","topic":"metric","lemma":"ticket_423_t10_line2_qed_or_qex","title":"#423 ticket-10 line 2: HAUSDORFF_DIRECTED / HAUSDORFF_SYMM attach as ADR-0006 adapters over the extracted exact rationals q_ddh_sq / q_hsymm_sq whose square roots are HausdorffDensify's directed_discrete_h and its symmetric max, JTS pair = 500 (QED); or the keyword pair stays a named missing constructor (QEX); discharged QED","file":"theories/HausdorffDiscreteQ.v","witness":"423-t10-oracle"} *)
Theorem ticket_423_t10_line2_qed_or_qex :
  (hausdorff_oracle_park_inhabits HausdorffOracleKeyword
   /\ q_ddh_sq jts_qA jts_qB = 500%Q)
  \/
  (~ hausdorff_oracle_park_inhabits HausdorffOracleKeyword).
Proof.
  left. split; [ | exact jts_q_ddh_sq_500 ].
  split; [ exact sqrt_q_ddh_sq | exact sqrt_q_hsymm_sq ].
Qed.

Print Assumptions q_ddh_sq.
Print Assumptions q_ddh_sq_R.
Print Assumptions q_hsymm_sq_R.
Print Assumptions jts_q_ddh_sq_500.
Print Assumptions ticket_423_t10_line2_qed_or_qex.
