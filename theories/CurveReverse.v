(* ============================================================================
   NetTopologySuite.Proofs.CurveReverse
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, rung 14a (issue #65): the REVERSAL layer --
   the machinery the open-chain two-sided cap walk (14b) traverses its
   right boundary with, and independently the SQL/MM ring-orientation
   flip (the hole convention: holes are shells traversed backwards).

     - `rev_arc` / `rev_segment` / `curve_ring_reverse`: reverse a
       three-point arc (swap start/end), a segment, and a whole ring
       (reverse the list AND each segment).

     - Geometry is traversal-invariant: `rev_arc_valid` (the
       non-collinearity cross only flips sign), `rev_arc_center` /
       `rev_arc_radius` (the circumcircle is the same -- center
       invariance via `equidistant_point_is_arc_center`, its FOURTH
       consumer).

     - The normal fields under reversal expose the ORIENTATION WART
       this layer exists to formalise: for ARCS the radial normal is
       traversal-agnostic (`arc_norm_rev_{end,start}`: the roles
       merely swap), but for CHORDS the `unit_perp` normal FLIPS SIGN
       (`chord_norm_rev`).  Consequently offsetting commutes with
       reversal at OPPOSITE signs per kind:

           offset (rev chord) d  =  rev (offset chord (-d))
           offset (rev arc)   d  =  rev (offset arc     d )

       (`offset_rev_chord` / `offset_rev_arc`).  This is the formal
       content of "the side of an offset is encoded by traversal
       orientation" -- true for chords, FALSE for raw three-point arcs
       -- and the reason JTS's OffsetCurveBuilder tracks an explicit
       side, which the 14b cap walk must thread accordingly.

     - HEADLINE `valid_curve_ring_reverse`: reversing a valid compound
       ring yields a valid compound ring (arc validity, adjacency and
       closedness all flip coherently).  With
       `curve_ring_reverse_length`.

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio).  No
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Vec Direction CurveGeometry Overlay ArcChordApprox.
From NTS.Proofs Require Import ArcOffsetThreePoint CurveRingOffset.
From NTS.Proofs Require Import CurveOffsetAssembly CurveLinearise BufferOffset.

Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Reversal of arcs, segments, rings.                                     *)
(* -------------------------------------------------------------------------- *)

Definition rev_arc (a : CircularArc) : CircularArc :=
  mkCircularArc (arc_end a) (arc_mid a) (arc_start a).

Definition rev_segment (s : CurveSegment) : CurveSegment :=
  match s with
  | CSChord p q => CSChord q p
  | CSArc a => CSArc (rev_arc a)
  end.

Definition curve_ring_reverse (r : CurveRing) : CurveRing :=
  map rev_segment (rev r).

Lemma rev_segment_start : forall s,
  curve_segment_start (rev_segment s) = curve_segment_end s.
Proof. intros [p q | a]; reflexivity. Qed.

Lemma rev_segment_end : forall s,
  curve_segment_end (rev_segment s) = curve_segment_start s.
Proof. intros [p q | a]; reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Geometry is traversal-invariant.                                       *)
(* -------------------------------------------------------------------------- *)

Lemma rev_arc_valid : forall a,
  valid_arc a -> valid_arc (rev_arc a).
Proof.
  intros a Hva.
  unfold valid_arc, rev_arc in *.
  cbn [arc_start arc_mid arc_end].
  cbv zeta in *.
  intros Heq. apply Hva. nra.
Qed.

Lemma rev_arc_center : forall a,
  valid_arc a -> arc_center (rev_arc a) = arc_center a.
Proof.
  intros a Hva.
  destruct (arc_center_equidistant a Hva) as [Hsm Hse].
  symmetry.
  apply (equidistant_point_is_arc_center (rev_arc a) (arc_center a)
           (rev_arc_valid a Hva)).
  - (* dist_sq C (start of rev = end a) = dist_sq C (mid a) *)
    cbn [rev_arc arc_start arc_mid]. lra.
  - (* dist_sq C (end a) = dist_sq C (start a) *)
    cbn [rev_arc arc_start arc_end]. lra.
Qed.

Lemma rev_arc_radius : forall a,
  valid_arc a -> arc_radius (rev_arc a) = arc_radius a.
Proof.
  intros a Hva.
  unfold arc_radius at 1.
  rewrite (rev_arc_center a Hva).
  cbn [rev_arc arc_start].
  apply (arc_center_dist_end a Hva).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Normal fields under reversal: arcs swap roles, chords flip sign.       *)
(* -------------------------------------------------------------------------- *)

Lemma arc_norm_rev_end : forall a,
  valid_arc a ->
  segment_norm_end (CSArc (rev_arc a)) = segment_norm_start (CSArc a).
Proof.
  intros a Hva.
  cbn [segment_norm_end segment_norm_start].
  rewrite (rev_arc_center a Hva), (rev_arc_radius a Hva).
  cbn [rev_arc arc_end].
  reflexivity.
Qed.

Lemma arc_norm_rev_start : forall a,
  valid_arc a ->
  segment_norm_start (CSArc (rev_arc a)) = segment_norm_end (CSArc a).
Proof.
  intros a Hva.
  cbn [segment_norm_start segment_norm_end].
  rewrite (rev_arc_center a Hva), (rev_arc_radius a Hva).
  cbn [rev_arc arc_start].
  reflexivity.
Qed.

(* Chord direction reverses, so the unit_perp normal flips sign.             *)
Lemma seg_vec_rev : forall p q,
  seg_vec q p = vneg (seg_vec p q).
Proof.
  intros p q. unfold seg_vec, vneg. apply Vec_eq; cbn [vx vy]; ring.
Qed.

Lemma vmag_vneg : forall v, vmag (vneg v) = vmag v.
Proof.
  intros v. unfold vmag. f_equal.
  unfold vmag_sq, vdot, vneg. cbn [vx vy]. ring.
Qed.

Lemma chord_norm_rev : forall p q,
  segment_norm_end (CSChord q p) =
  vneg (segment_norm_end (CSChord p q)).
Proof.
  intros p q.
  cbn [segment_norm_end].
  unfold unit_perp.
  rewrite (seg_vec_rev p q).
  rewrite (vmag_vneg (seg_vec p q)).
  apply Vec_eq; unfold vscale, vperp, vneg; cbn [vx vy]; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  THE ORIENTATION WART: offsetting commutes with reversal at OPPOSITE    *)
(*     signs per segment kind.                                                *)
(* -------------------------------------------------------------------------- *)

(* Chords: the reversed chord's +d offset is the original's -d offset,       *)
(* reversed (the unit_perp normal flips with traversal).                      *)
Lemma offset_rev_chord : forall (p q : Point) (d : R),
  curve_segment_offset (rev_segment (CSChord p q)) d =
  rev_segment (curve_segment_offset (CSChord p q) (- d)).
Proof.
  intros p q d.
  cbn [rev_segment curve_segment_offset].
  assert (Hpt : forall X : Point,
             offset_point q p X d = offset_point p q X (- d)).
  { intros X.
    unfold offset_point, offset_normal, unit_perp, pt_translate.
    rewrite (seg_vec_rev p q).
    rewrite (vmag_vneg (seg_vec p q)).
    apply point_eq; unfold vscale, vperp, vneg; cbn [px py vx vy]; ring. }
  rewrite (Hpt q), (Hpt p). reflexivity.
Qed.

(* Arcs: the radial normal is traversal-agnostic, so the reversed arc's      *)
(* +d offset is the original's +d offset, reversed -- the SAME sign.          *)
Lemma offset_rev_arc : forall (a : CircularArc) (d : R),
  valid_arc a ->
  curve_segment_offset (rev_segment (CSArc a)) d =
  rev_segment (curve_segment_offset (CSArc a) d).
Proof.
  intros a d Hva.
  cbn [rev_segment curve_segment_offset].
  unfold arc_offset_arc.
  rewrite (rev_arc_center a Hva), (rev_arc_radius a Hva).
  cbn [rev_arc arc_start arc_mid arc_end].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Ring reversal preserves validity.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma curve_ring_reverse_length : forall r,
  length (curve_ring_reverse r) = length r.
Proof.
  intros r. unfold curve_ring_reverse.
  rewrite length_map, length_rev. reflexivity.
Qed.

Lemma curve_ring_reverse_nonnil : forall s rest,
  curve_ring_reverse (s :: rest) <> [].
Proof.
  intros s rest H.
  apply (f_equal (@length CurveSegment)) in H.
  rewrite curve_ring_reverse_length in H. discriminate.
Qed.

Lemma curve_ring_reverse_cons : forall s rest,
  curve_ring_reverse (s :: rest) =
  curve_ring_reverse rest ++ [rev_segment s].
Proof.
  intros s rest. unfold curve_ring_reverse. cbn [rev].
  rewrite map_app. reflexivity.
Qed.

Lemma curve_ring_reverse_last : forall s rest dflt,
  last (curve_ring_reverse (s :: rest)) dflt = rev_segment s.
Proof.
  intros s rest dflt. rewrite curve_ring_reverse_cons. apply last_snoc.
Qed.

Lemma curve_ring_reverse_hd : forall s rest dflt,
  hd dflt (curve_ring_reverse (s :: rest)) =
  rev_segment (last (s :: rest) s).
Proof.
  intros s rest; revert s.
  induction rest as [| b rest' IH]; intros s dflt.
  - reflexivity.
  - rewrite curve_ring_reverse_cons.
    destruct (curve_ring_reverse (b :: rest')) as [| m M'] eqn:EM;
      [ exact (False_ind _ (curve_ring_reverse_nonnil b rest' EM)) | ].
    cbn [app hd].
    rewrite (last_cons_cons s b rest').
    change m with (hd dflt (m :: M')).
    rewrite <- EM.
    rewrite (IH b dflt).
    f_equal.
    apply last_default_irrel. discriminate.
Qed.

Lemma curve_ring_reverse_arcs_valid : forall r,
  curve_ring_arcs_valid r ->
  curve_ring_arcs_valid (curve_ring_reverse r).
Proof.
  intros r Hv.
  unfold curve_ring_reverse, curve_ring_arcs_valid in *.
  apply Forall_forall. intros x Hin.
  apply in_map_iff in Hin. destruct Hin as [s [Hxs Hin]].
  apply in_rev in Hin.
  subst x.
  pose proof (proj1 (Forall_forall _ _) Hv s Hin) as Hs.
  destruct s as [p q | a]; cbn [rev_segment].
  - exact I.
  - apply rev_arc_valid. exact Hs.
Qed.

Lemma curve_ring_reverse_adjacent : forall r,
  curve_ring_adjacent r ->
  curve_ring_adjacent (curve_ring_reverse r).
Proof.
  induction r as [| s rest IH]; intros Hadj.
  - exact I.
  - rewrite curve_ring_reverse_cons.
    destruct rest as [| s2 rest'].
    + exact I.
    + destruct Hadj as [Hj Hadj'].
      apply (curve_ring_adjacent_snoc _ _ (rev_segment s)).
      * apply curve_ring_reverse_nonnil.
      * apply IH. exact Hadj'.
      * rewrite (curve_ring_reverse_last s2 rest').
        rewrite rev_segment_end, rev_segment_start.
        symmetry. exact Hj.
Qed.

Lemma curve_ring_reverse_closed : forall r,
  curve_ring_closed r ->
  curve_ring_closed (curve_ring_reverse r).
Proof.
  intros [| s0 rest] Hcl; [ exact Hcl | ].
  unfold curve_ring_closed in Hcl.
  destruct (curve_ring_reverse (s0 :: rest)) as [| h R'] eqn:ER;
    [ exact (False_ind _ (curve_ring_reverse_nonnil s0 rest ER)) | ].
  unfold curve_ring_closed.
  assert (Hh : h = rev_segment (last (s0 :: rest) s0)).
  { change h with (hd h (h :: R')). rewrite <- ER.
    apply curve_ring_reverse_hd. }
  assert (Hl : last (h :: R') h = rev_segment s0).
  { rewrite <- ER. apply curve_ring_reverse_last. }
  rewrite Hl, Hh.
  rewrite rev_segment_end, rev_segment_start.
  symmetry. exact Hcl.
Qed.

(* HEADLINE: reversal preserves compound-ring validity (the SQL/MM           *)
(* ring-orientation flip).                                                    *)
Theorem valid_curve_ring_reverse : forall r,
  valid_curve_ring r ->
  valid_curve_ring (curve_ring_reverse r).
Proof.
  intros r [Hv [Hadj Hcl]].
  split; [ | split ].
  - apply curve_ring_reverse_arcs_valid. exact Hv.
  - apply curve_ring_reverse_adjacent. exact Hadj.
  - apply curve_ring_reverse_closed. exact Hcl.
Qed.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions rev_arc_center.
Print Assumptions chord_norm_rev.
Print Assumptions offset_rev_chord.
Print Assumptions offset_rev_arc.
Print Assumptions valid_curve_ring_reverse.
