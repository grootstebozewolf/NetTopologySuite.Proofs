(* ============================================================================
   NetTopologySuite.Proofs.DirectedApprox
   ----------------------------------------------------------------------------
   PROBE for the "directed approximation" spec pattern (see
   docs/directed-approximation-2026-11.md for the experiment and its verdict).

   A compute predicate `comp` approximates a spec predicate `spec` on a domain
   `D` in one of two directions:

     over  (complete): spec => comp   -- never drops a real hit
     under (sound)   : comp => spec   -- never invents a hit
     exact           : both           -- gap 0 (integer-lane kernel)

   plus an optional GAP BOUND for the over direction: every accepted point is
   within eps of a spec point (comp subset of the eps-neighbourhood of spec).

   No Axiom / Admitted.  Pure Prop, no Flocq.
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

Section Directed.
  Context {X : Type}.

  Definition over_on (D : X -> Prop) (spec comp : X -> Prop) : Prop :=
    forall x, D x -> spec x -> comp x.

  Definition under_on (D : X -> Prop) (spec comp : X -> Prop) : Prop :=
    forall x, D x -> comp x -> spec x.

  Definition exact_on (D : X -> Prop) (spec comp : X -> Prop) : Prop :=
    forall x, D x -> (spec x <-> comp x).

  (* Gap bound with respect to a distance relation `d`: every accepted x is
     within eps of some spec point.  This is the one-sided Hausdorff half
     `comp subset N_eps(spec)`. *)
  Definition gap_within (d : X -> X -> R) (eps : R) (D : X -> Prop)
             (spec comp : X -> Prop) : Prop :=
    forall x, D x -> comp x -> exists y, spec y /\ d x y <= eps.

  Lemma exact_iff_over_under :
    forall D spec comp,
      exact_on D spec comp <-> over_on D spec comp /\ under_on D spec comp.
  Proof.
    unfold exact_on, over_on, under_on. intros D spec comp. split.
    - intros H. split; intros x Hx; apply (H x Hx).
    - intros [Ho Hu] x Hx. split; [apply Ho | apply Hu]; exact Hx.
  Qed.

  (* Trivial gap: an exact predicate has gap 0 when d is reflexive. *)
  Lemma under_gap_zero :
    forall d D spec comp,
      (forall x, d x x <= 0) ->
      under_on D spec comp -> gap_within d 0 D spec comp.
  Proof.
    intros d D spec comp Hd Hu x Hx Hc. exists x. split; [apply Hu; auto | apply Hd].
  Qed.

  (* ---- composition along a chain of approximations ---------------------- *)

  Lemma over_trans :
    forall D s m c, over_on D s m -> over_on D m c -> over_on D s c.
  Proof. unfold over_on; intros; auto. Qed.

  Lemma under_trans :
    forall D s m c, under_on D s m -> under_on D m c -> under_on D s c.
  Proof. unfold under_on; intros; auto. Qed.

  (* Gap composition: bounds add under the triangle inequality. *)
  Lemma gap_trans :
    forall (d : X -> X -> R) e1 e2 D s m c,
      (forall a b c', d a c' <= d a b + d b c') ->
      gap_within d e1 D m c ->
      gap_within d e2 (fun _ => True) s m ->
      gap_within d (e1 + e2) D s c.
  Proof.
    intros d e1 e2 D s m c Htri H1 H2 x Hx Hc.
    destruct (H1 x Hx Hc) as [y [Hmy Hxy]].
    destruct (H2 y I Hmy) as [z [Hsz Hyz]].
    exists z. split; [exact Hsz|]. specialize (Htri x y z). lra.
  Qed.

  (* gap_within only constrains accepted points, so it is monotone in comp and
     closed under union: this is the entire content of ArcOverlay's case split. *)
  Lemma gap_mono_comp :
    forall d eps D spec c c',
      (forall x, D x -> c' x -> c x) ->
      gap_within d eps D spec c -> gap_within d eps D spec c'.
  Proof. unfold gap_within; intros; eauto. Qed.

  Lemma gap_or :
    forall d eps D spec c1 c2,
      gap_within d eps D spec c1 -> gap_within d eps D spec c2 ->
      gap_within d eps D spec (fun x => c1 x \/ c2 x).
  Proof. unfold gap_within; intros d eps D spec c1 c2 H1 H2 x Hx [h|h]; eauto. Qed.

  (* ---- boolean connectives (the overlay assembly) ----------------------- *)

  Lemma over_and :
    forall D s1 c1 s2 c2,
      over_on D s1 c1 -> over_on D s2 c2 ->
      over_on D (fun x => s1 x /\ s2 x) (fun x => c1 x /\ c2 x).
  Proof. unfold over_on; intros D s1 c1 s2 c2 H1 H2 x Hx [a b]; auto. Qed.

  Lemma over_or :
    forall D s1 c1 s2 c2,
      over_on D s1 c1 -> over_on D s2 c2 ->
      over_on D (fun x => s1 x \/ s2 x) (fun x => c1 x \/ c2 x).
  Proof. unfold over_on; intros D s1 c1 s2 c2 H1 H2 x Hx [a|b]; auto. Qed.

  Lemma under_and :
    forall D s1 c1 s2 c2,
      under_on D s1 c1 -> under_on D s2 c2 ->
      under_on D (fun x => s1 x /\ s2 x) (fun x => c1 x /\ c2 x).
  Proof. unfold under_on; intros D s1 c1 s2 c2 H1 H2 x Hx [a b]; auto. Qed.

  Lemma under_or :
    forall D s1 c1 s2 c2,
      under_on D s1 c1 -> under_on D s2 c2 ->
      under_on D (fun x => s1 x \/ s2 x) (fun x => c1 x \/ c2 x).
  Proof. unfold under_on; intros D s1 c1 s2 c2 H1 H2 x Hx [a|b]; auto. Qed.

  (* Negation FLIPS the direction -- this is the whole reason mixed pipelines
     need a bound lemma. *)
  Lemma over_not_of_under :
    forall D s c, under_on D s c ->
      over_on D (fun x => ~ s x) (fun x => ~ c x).
  Proof. unfold over_on, under_on; intros D s c H x Hx Hns Hc; apply Hns; auto. Qed.

  Lemma under_not_of_over :
    forall D s c, over_on D s c ->
      under_on D (fun x => ~ s x) (fun x => ~ c x).
  Proof. unfold over_on, under_on; intros D s c H x Hx Hnc Hs; apply Hnc; auto. Qed.

  (* Difference A \ B = A /\ ~B: over needs (A over, B UNDER). *)
  Lemma over_diff :
    forall D sA cA sB cB,
      over_on D sA cA -> under_on D sB cB ->
      over_on D (fun x => sA x /\ ~ sB x) (fun x => cA x /\ ~ cB x).
  Proof.
    intros. apply over_and; [assumption | apply over_not_of_under; assumption].
  Qed.

End Directed.
Close Scope R_scope.

(* The mixed case has NO guarantee: with A exact and B merely OVER, the
   difference A \ B is not over.  Concrete witness on X := bool. *)
Lemma over_diff_needs_under :
  exists (sA cA sB cB : bool -> Prop),
    over_on (fun _ => True) sA cA /\ over_on (fun _ => True) sB cB /\
    ~ over_on (fun _ => True)
        (fun x => sA x /\ ~ sB x) (fun x => cA x /\ ~ cB x).
Proof.
  exists (fun _ => True), (fun _ => True), (fun x => x = true), (fun _ => True).
  split; [intros x _ H; exact H|]. split; [intros x _ _; exact I|].
  intro H. specialize (H false I). simpl in H.
  assert (Hs : True /\ ~ (false = true)) by (split; [exact I | discriminate]).
  destruct (H Hs) as [_ Hn]. apply Hn. exact I.
Qed.

(* ---- Signed-bulge region model (per-arc direction) -----------------------
   A curved region R differs from its chord polygon P by circular segments:
   out-bulging ones O are added, in-bulging ones I are carved away:
       R = (P \/ O) \ I.
   That decomposition is the *assumed* (Jordan-class) hypothesis; given it,
   the direction of the chord approximation is pure set logic.  The "true
   region" is `spec`, the chord polygon is `comp`. *)
Section SignedBulge.
  Context {X : Type}.
  Variables (P O Ib : X -> Prop).
  Let R (x : X) : Prop := (P x \/ O x) /\ ~ Ib x.

  (* No in-bulging arcs: the chord polygon under-approximates R. *)
  Lemma chord_under_of_no_in :
    (forall x, ~ Ib x) -> under_on (fun _ => True) R P.
  Proof. intros H x _ Hp. split; [left; exact Hp | apply H]. Qed.

  (* No out-bulging arcs (O inside P): the chord polygon over-approximates R. *)
  Lemma chord_over_of_no_out :
    (forall x, O x -> P x) -> over_on (fun _ => True) R P.
  Proof. intros H x _ [[Hp|Ho] _]; [exact Hp | apply H, Ho]. Qed.

  (* Mixed: one out-segment point outside P and not carved, plus one carved
     point of P => the chord polygon is neither over nor under. *)
  Lemma chord_neither_of_mixed :
    (exists o, O o /\ ~ P o /\ ~ Ib o) ->
    (exists i, Ib i /\ P i) ->
    ~ over_on (fun _ => True) R P /\ ~ under_on (fun _ => True) R P.
  Proof.
    intros (o & Ho & Hnp & Hni) (i & Hi & Hpi). split.
    - intro H. apply Hnp, (H o I). split; [right; exact Ho | exact Hni].
    - intro H. destruct (H i I Hpi) as [_ Hn]. exact (Hn Hi).
  Qed.
End SignedBulge.
