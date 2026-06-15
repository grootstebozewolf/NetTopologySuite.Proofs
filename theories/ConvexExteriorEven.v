(* ============================================================================
   NetTopologySuite.Proofs.ConvexExteriorEven
   ----------------------------------------------------------------------------
   Convex-chain monotonicity campaign: the GENERAL exterior-even, factoring the
   parity plumbing out of every family.

   `ConvexOffringSeam.convex_parity_seam_offring_of` assembles the total off-ring
   seam for a half-plane-presented ring from two guarded-parity obligations:
   interior-odd (`0 < conv_min ⟹ point_in_ring`) — which is GENERAL
   (`MonotoneChainCoverage.interior_hits_one_chain_of_edge_hps`) — and
   exterior-even (`conv_min < 0 ⟹ ~ point_in_ring`), which has so far been
   supplied PER FAMILY (e.g. `HexagonOffringSeam.hexagon_exterior_even`, a
   six-edge per-band analysis).

   This file isolates the GEOMETRIC heart of exterior-even as one named predicate
   — `convex_exterior_balanced`: an exterior point's rightward ray crosses the two
   monotone chains BOTH-or-NEITHER — and proves, once and for all, that this
   predicate yields `~ point_in_ring` for any `bimonotone_split` ring (via the
   parity bridge `MonotoneChainParity.bimonotone_split_parity`).  The converse
   shows the predicate is exactly the per-family obligation, repackaged through
   the bridge; so every family now only owes the geometric balance, not the
   parity reduction.  Validated on the diamond and hexagon (recovered from their
   existing exterior-even lemmas), and composed into a general convex off-ring
   seam (`convex_offring_seam_of_balanced`).

   The genuinely-hard geometric discharge of `convex_exterior_balanced` for an
   ARBITRARY convex ring (the convex "horizontal slice = inter-chain interval"
   fact) remains the open content — but note the exterior straddle-extraction
   lever the interior proof uses (`conv_min > 0` forcing vertex-height avoidance)
   is unavailable for exterior points, so it is a genuine multi-session lemma; it
   is carried here as the named predicate, never `Admitted`.

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia.
From NTS.Proofs Require Import Distance Overlay MonotoneChainParity
                               MonotoneChainConstruction ConvexChainSplit
                               MonotoneChainCoverage
                               ConvexField PointInRingTangents PointInRingCorrect
                               JCT_OnEdgeCounterexample ConvexOffringSeam
                               ConvexSlice
                               DiamondOffringSeam HexagonOffringSeam.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  `chain_crossed` is decidable (via the crossing count), so "not XOR"      *)
(*     collapses to the iff.                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma chain_crossed_dec : forall p es, chain_crossed p es \/ ~ chain_crossed p es.
Proof.
  intros p es. destruct (Nat.eq_dec (cross_count p es) 0) as [H | H].
  - right. rewrite chain_crossed_iff_count. lia.
  - left. apply chain_crossed_iff_count. exact H.
Qed.

Lemma not_xor_iff : forall A B : Prop,
  (A \/ ~ A) -> (B \/ ~ B) ->
  ~ ((A /\ ~ B) \/ (~ A /\ B)) -> (A <-> B).
Proof. intros A B HA HB H. tauto. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The named geometric residual: exterior ⟹ both-or-neither chain crossed. *)
(* -------------------------------------------------------------------------- *)

Definition convex_exterior_balanced
    (r : Ring) (hps : list (R*R*R)) (inc dec : list Edge) : Prop :=
  forall p : Point,
    conv_min hps p < 0 ->
    ray_avoids_vertices p r ->
    no_horizontal_edge_at p r ->
    (chain_crossed p inc <-> chain_crossed p dec).

(* -------------------------------------------------------------------------- *)
(* §3  The general exterior-even: balance ⟹ ~ point_in_ring, for any split.    *)
(* -------------------------------------------------------------------------- *)

(* The parity plumbing, factored out of every family: a `bimonotone_split` ring
   whose exterior crossings are balanced has even ray-parity outside, i.e. is not
   `point_in_ring`.  (`bimonotone_split_parity` makes `point_in_ring` the XOR of
   the two chain crossings; balance negates the XOR.) *)
Theorem convex_exterior_even_of_balanced : forall r inc dec hps p,
  bimonotone_split r inc dec ->
  convex_exterior_balanced r hps inc dec ->
  conv_min hps p < 0 ->
  ray_avoids_vertices p r ->
  no_horizontal_edge_at p r ->
  ~ point_in_ring p r.
Proof.
  intros r inc dec hps p Hbs Hbal Hext Hrav Hnh Hpir.
  apply (proj1 (bimonotone_split_parity r inc dec p Hbs)) in Hpir.
  destruct (Hbal p Hext Hrav Hnh) as [Hid Hdi].
  destruct Hpir as [[Hi Hnd] | [Hni Hd]].
  - exact (Hnd (Hid Hi)).
  - exact (Hni (Hdi Hd)).
Qed.

(* The converse: the named predicate is EXACTLY the per-family exterior-even
   obligation, viewed through the parity bridge.  So generalising via
   `convex_exterior_balanced` loses nothing — it factors the bridge step out. *)
Theorem balanced_of_exterior_even : forall r inc dec hps,
  bimonotone_split r inc dec ->
  (forall p, conv_min hps p < 0 -> ray_avoids_vertices p r ->
             no_horizontal_edge_at p r -> ~ point_in_ring p r) ->
  convex_exterior_balanced r hps inc dec.
Proof.
  intros r inc dec hps Hbs Hext p Hcm Hrav Hnh.
  pose proof (Hext p Hcm Hrav Hnh) as Hn.
  rewrite (bimonotone_split_parity r inc dec p Hbs) in Hn.
  apply not_xor_iff; [ apply chain_crossed_dec | apply chain_crossed_dec | exact Hn ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The capstone: a general convex off-ring seam from the balance predicate. *)
(* -------------------------------------------------------------------------- *)

(* Feeding the general exterior-even into `convex_parity_seam_offring_of`: any
   half-plane-presented `bimonotone_split` ring with the balance predicate (and
   the general interior-odd obligation + the presentation facts) gets the TOTAL
   off-ring parity seam.  Exterior-even is now supplied generically; only the
   interior obligation and presentation remain per-instance. *)
Theorem convex_offring_seam_of_balanced : forall r hps inc dec p M,
  bimonotone_split r inc dec ->
  (forall pt, conv_min hps pt = 0 -> ring_image r pt) ->
  Forall (vertices_in_halfplane r) hps ->
  Forall (fun hp : R * R * R => let '(a, b, _) := hp in 0 < a * a + b * b) hps ->
  0 < M ->
  (forall pt, 0 < conv_min hps pt -> px pt * px pt + py pt * py pt <= M * M) ->
  convex_exterior_balanced r hps inc dec ->
  (0 < conv_min hps p -> ray_avoids_vertices p r ->
     no_horizontal_edge_at p r -> point_in_ring p r) ->
  parity_characterises_interior_cont_offring p r.
Proof.
  intros r hps inc dec p M Hbs Hzero Hverts Hnd HM Hbound Hbal Hint.
  apply (convex_parity_seam_offring_of r hps p M Hzero Hverts Hnd HM Hbound Hint).
  intros Hext Hrav Hnh.
  exact (convex_exterior_even_of_balanced r inc dec hps p Hbs Hbal Hext Hrav Hnh).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Validation: the diamond and hexagon discharge the balance predicate.    *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_exterior_balanced :
  convex_exterior_balanced diamond_ring diamond_hps diamond_inc diamond_dec.
Proof.
  apply balanced_of_exterior_even.
  - exact diamond_bimonotone.
  - exact diamond_exterior_even.
Qed.

Lemma hexagon_exterior_balanced :
  convex_exterior_balanced hexagon_ring hexagon_edge_hps hexagon_inc hexagon_dec.
Proof.
  apply balanced_of_exterior_even.
  - exact hexagon_bimonotone.
  - exact hexagon_exterior_even.
Qed.

(* Round-trip sanity: the general theorem recovers each family's exterior-even. *)
Corollary diamond_exterior_even_via_balanced : forall p,
  conv_min diamond_hps p < 0 ->
  ray_avoids_vertices p diamond_ring ->
  no_horizontal_edge_at p diamond_ring ->
  ~ point_in_ring p diamond_ring.
Proof.
  intros p. apply (convex_exterior_even_of_balanced diamond_ring diamond_inc diamond_dec
                     diamond_hps p diamond_bimonotone diamond_exterior_balanced).
Qed.

Corollary hexagon_exterior_even_via_balanced : forall p,
  conv_min hexagon_edge_hps p < 0 ->
  ray_avoids_vertices p hexagon_ring ->
  no_horizontal_edge_at p hexagon_ring ->
  ~ point_in_ring p hexagon_ring.
Proof.
  intros p. apply (convex_exterior_even_of_balanced hexagon_ring hexagon_inc hexagon_dec
                     hexagon_edge_hps p hexagon_bimonotone hexagon_exterior_balanced).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The EXTERIOR COMPANION: balance discharged generally via the slice fact.*)
(* -------------------------------------------------------------------------- *)

(* Height bounds on monotone vertex lists. *)
Lemma y_strict_incr_le_last : forall (l : list Point) (v : Point),
  y_strict_incr l -> In v l -> py v <= py (last l dpt).
Proof.
  induction l as [| a l' IH]; intros v Hinc Hin; [ inversion Hin | ].
  destruct l' as [| b l''].
  - destruct Hin as [<- | []]. cbn [last]. lra.
  - destruct Hinc as [Hab Hinc']. destruct Hin as [<- | Hin].
    + pose proof (IH b Hinc' (or_introl eq_refl)) as Hb. cbn [last] in *. lra.
    + cbn [last]. apply IH; assumption.
Qed.

Lemma y_strict_incr_hd_le : forall (l : list Point) (v : Point),
  y_strict_incr l -> In v l -> py (hd dpt l) <= py v.
Proof.
  intros l v Hinc Hin. destruct l as [| a l']; [ inversion Hin | ]. cbn [hd].
  revert a v Hinc Hin. induction l' as [| b l'' IH]; intros a v Hinc Hin.
  - destruct Hin as [<- | []]. lra.
  - destruct Hin as [<- | Hin]; [ lra | ].
    destruct Hinc as [Hab Hinc']. pose proof (IH b v Hinc' Hin) as Hbv. lra.
Qed.

Lemma y_strict_decr_le_hd : forall (l : list Point) (v : Point),
  y_strict_decr l -> In v l -> py v <= py (hd dpt l).
Proof.
  intros l v Hdec Hin. destruct l as [| a l']; [ inversion Hin | ]. cbn [hd].
  revert a v Hdec Hin. induction l' as [| b l'' IH]; intros a v Hdec Hin.
  - destruct Hin as [<- | []]. lra.
  - destruct Hin as [<- | Hin]; [ lra | ].
    destruct Hdec as [Hba Hdec']. pose proof (IH b v Hdec' Hin) as Hbv. lra.
Qed.

Lemma y_strict_decr_last_le : forall (l : list Point) (v : Point),
  y_strict_decr l -> In v l -> py (last l dpt) <= py v.
Proof.
  induction l as [| a l' IH]; intros v Hdec Hin; [ inversion Hin | ].
  destruct l' as [| b l''].
  - destruct Hin as [<- | []]. cbn [last]. lra.
  - destruct Hdec as [Hba Hdec']. destruct Hin as [<- | Hin].
    + pose proof (IH b Hdec' (or_introl eq_refl)) as Hb. cbn [last] in *. lra.
    + cbn [last]. apply IH; assumption.
Qed.

(* Positional contradiction (the dec-crossed/inc-not impossibility): a point not
   inward of the straddling UP edge (slack <= 0) cannot be strictly left of the
   straddling DOWN edge (slack < 0) — the left chain is left of the right chain.
   Proof via the on-edge image point of e_d in e_i's half-plane (slice helpers). *)
Lemma slice_x_contra :
  forall (r : Ring) (hps : list (R * R * R)) (q : Point) (e_i e_d : Edge),
    Forall (vertices_in_halfplane r) hps ->
    In (edge_inward_hp e_i) hps ->
    In e_d (ring_edges r) ->
    py (fst e_i) < py (snd e_i) ->
    py (snd e_d) < py (fst e_d) ->
    straddles q e_d ->
    hp_slack (edge_inward_hp e_i) q <= 0 ->
    hp_slack (edge_inward_hp e_d) q < 0 ->
    False.
Proof.
  intros r hps q e_i e_d Hverts HiHps HdIn Hup Hdn Hstrd Hsi Hsd.
  destruct (straddle_point_ring_image r e_d q HdIn Hstrd) as [m [Hm_img [Hm_y Hm_0]]].
  rewrite Forall_forall in Hverts.
  pose proof (image_slack_nonneg r (edge_inward_hp e_i) m (Hverts _ HiHps) Hm_img) as Hmi.
  pose proof (hp_slack_sub_x (edge_inward_hp e_i) q m (eq_sym Hm_y)) as Hsub_i.
  pose proof (hp_slack_sub_x (edge_inward_hp e_d) q m (eq_sym Hm_y)) as Hsub_d.
  rewrite (edge_inward_hp_xcoef e_i) in Hsub_i.
  rewrite (edge_inward_hp_xcoef e_d) in Hsub_d.
  rewrite Hm_0 in Hsub_d.
  nra.
Qed.

(* The exterior companion to `interior_hits_one_chain_of_edge_hps`: for an
   exterior point of a y-unimodal convex ring in full general position, the two
   chains are crossed BOTH-or-NEITHER. *)
Theorem convex_exterior_balanced_of_unimodal :
  forall (up down : list Point) (apex bottom : Point)
         (hps : list (R * R * R)) (q : Point) (outer : Ring),
    let inc := ring_edges (up ++ [apex]) in
    let dec := ring_edges (apex :: down) in
    y_strict_incr (up ++ [apex]) ->
    y_strict_decr (apex :: down) ->
    (2 <= length (up ++ [apex]))%nat ->
    (2 <= length (apex :: down))%nat ->
    Forall (vertices_in_halfplane outer) hps ->
    Forall (fun e => In (edge_inward_hp e) hps) inc ->
    py (hd dpt (up ++ [apex])) = py bottom ->
    py (last (apex :: down) dpt) = py bottom ->
    last (up ++ [apex]) dpt = apex ->
    outer = up ++ apex :: down ->
    conv_min hps q < 0 ->
    (forall v, In v outer -> py v <> py q) ->
    (chain_crossed q inc <-> chain_crossed q dec).
Proof.
  intros up down apex bottom hps q outer inc dec
         Hinc Hdec Hleni Hlend Hverts HincHps Hhd Hlastd Hlasti Houter Hext Hav.
  assert (Hbs : bimonotone_split outer inc dec).
  { rewrite Houter. apply bimonotone_split_unimodal; assumption. }
  destruct Hbs as [Hsplit [Hci Hcd]].
  assert (HinInc : forall e, In e inc -> In e (ring_edges outer))
    by (intros e He; rewrite Hsplit; apply in_or_app; left; exact He).
  assert (HinDec : forall e, In e dec -> In e (ring_edges outer))
    by (intros e He; rewrite Hsplit; apply in_or_app; right; exact He).
  assert (HavI : forall v, In v (up ++ [apex]) -> py v <> py q).
  { intros v Hv. apply Hav. rewrite Houter, in_app_iff.
    rewrite in_app_iff in Hv. destruct Hv as [Hvup | Hvap].
    - left; exact Hvup.
    - right. destruct Hvap as [<- | []]. left; reflexivity. }
  assert (HavD : forall v, In v (apex :: down) -> py v <> py q).
  { intros v Hv. apply Hav. rewrite Houter, in_app_iff. right.
    destruct Hv as [<- | Hv]; [ left; reflexivity | right; exact Hv ]. }
  pose proof (chain_increasing_all_up _ Hci) as Hallup.
  pose proof (chain_decreasing_all_dn _ Hcd) as Halldn.
  rewrite Forall_forall in Hallup, Halldn.
  split.
  - (* inc crossed -> dec crossed, via the slice fact + conv_min < 0 *)
    intros [ei [HeiIn Hcr]].
    pose proof (Hallup ei HeiIn) as HeiUp. unfold edge_up in HeiUp.
    pose proof (crossed_straddles q ei Hcr) as Hstr_i.
    pose proof (up_straddle_lo_hi q ei HeiUp Hstr_i) as [Hlo_i Hhi_i].
    destruct (ring_edges_endpoints_in (up ++ [apex]) ei HeiIn) as [HfiIn HsiIn].
    assert (Hqlt : py q < py apex).
    { pose proof (y_strict_incr_le_last (up ++ [apex]) (snd ei) Hinc HsiIn) as Hb.
      rewrite Hlasti in Hb. lra. }
    assert (Hqgt : py bottom < py q).
    { pose proof (y_strict_incr_hd_le (up ++ [apex]) (fst ei) Hinc HfiIn) as Hb.
      rewrite Hhd in Hb. lra. }
    destruct (chain_decreasing_straddles_y (apex :: down) q Hdec Hlend
                ltac:(rewrite Hlastd; exact Hqgt) ltac:(cbn [hd]; exact Hqlt) HavD)
      as [ed [HedIn Hstr_d]].
    destruct (chain_crossed_dec q dec) as [Hdc | Hndc]; [ exact Hdc | exfalso ].
    pose proof (Halldn ed HedIn) as HedDn. unfold edge_dn in HedDn.
    assert (Hned : ~ edge_crosses_ray q ed) by (intro Hc; apply Hndc; exists ed; auto).
    pose proof (dn_straddle_hi_lo q ed HedDn Hstr_d) as [Hd_hi Hd_lo].
    destruct ed as [[ex ey] [fx fy]]; cbn [fst snd px py] in *.
    destruct ei as [[axx ayy] [bxx byy]]; cbn [fst snd px py] in *.
    assert (Hsi : 0 < hp_slack (edge_inward_hp (mkPoint axx ayy, mkPoint bxx byy)) q).
    { destruct (edge_up_crosses_iff_hp axx ayy bxx byy q ltac:(lra)) as [Hfwd _].
      exact (proj2 (Hfwd Hcr)). }
    assert (Hsd : 0 <= hp_slack (edge_inward_hp (mkPoint ex ey, mkPoint fx fy)) q).
    { destruct (edge_dn_crosses_iff_hp ex ey fx fy q ltac:(lra)) as [_ Hback].
      destruct (Rle_or_lt 0 (hp_slack (edge_inward_hp (mkPoint ex ey, mkPoint fx fy)) q))
        as [HH | HH]; [ exact HH | exfalso; apply Hned; apply Hback; split; [ lra | exact HH ] ]. }
    pose proof (convex_slice_all_halfplanes outer hps q
                  (mkPoint axx ayy, mkPoint bxx byy) (mkPoint ex ey, mkPoint fx fy)
                  Hverts (HinInc _ HeiIn) (HinDec _ HedIn)
                  ltac:(cbn [fst snd py]; lra) ltac:(cbn [fst snd py]; lra)
                  Hstr_i Hstr_d Hsi Hsd) as Hall.
    pose proof (conv_min_nonneg_local hps q Hall) as Hcm. lra.
  - (* dec crossed -> inc crossed, via the positional contradiction slice_x_contra *)
    intros [ed [HedIn Hcr]].
    pose proof (Halldn ed HedIn) as HedDn. unfold edge_dn in HedDn.
    pose proof (crossed_straddles q ed Hcr) as Hstr_d.
    pose proof (dn_straddle_hi_lo q ed HedDn Hstr_d) as [Hd_hi Hd_lo].
    destruct (ring_edges_endpoints_in (apex :: down) ed HedIn) as [HfdIn HsdIn].
    assert (Hqlt : py q < py apex).
    { pose proof (y_strict_decr_le_hd (apex :: down) (fst ed) Hdec HfdIn) as Hb.
      cbn [hd] in Hb. lra. }
    assert (Hqgt : py bottom < py q).
    { pose proof (y_strict_decr_last_le (apex :: down) (snd ed) Hdec HsdIn) as Hb.
      rewrite Hlastd in Hb. lra. }
    destruct (chain_increasing_straddles_y (up ++ [apex]) q Hinc Hleni
                ltac:(rewrite Hhd; exact Hqgt) ltac:(rewrite Hlasti; exact Hqlt) HavI)
      as [ei [HeiIn Hstr_i]].
    destruct (chain_crossed_dec q inc) as [Hic | Hnic]; [ exact Hic | exfalso ].
    pose proof (Hallup ei HeiIn) as HeiUp. unfold edge_up in HeiUp.
    assert (Hnei : ~ edge_crosses_ray q ei) by (intro Hc; apply Hnic; exists ei; auto).
    pose proof (up_straddle_lo_hi q ei HeiUp Hstr_i) as [Hi_lo Hi_hi].
    rewrite Forall_forall in HincHps. pose proof (HincHps ei HeiIn) as HeiHps.
    destruct ei as [[axx ayy] [bxx byy]]; cbn [fst snd px py] in *.
    destruct ed as [[ex ey] [fx fy]]; cbn [fst snd px py] in *.
    assert (Hsi : hp_slack (edge_inward_hp (mkPoint axx ayy, mkPoint bxx byy)) q <= 0).
    { destruct (edge_up_crosses_iff_hp axx ayy bxx byy q ltac:(lra)) as [_ Hback].
      destruct (Rle_or_lt (hp_slack (edge_inward_hp (mkPoint axx ayy, mkPoint bxx byy)) q) 0)
        as [HH | HH]; [ exact HH | exfalso; apply Hnei; apply Hback; split; [ lra | exact HH ] ]. }
    assert (Hsd : hp_slack (edge_inward_hp (mkPoint ex ey, mkPoint fx fy)) q < 0).
    { destruct (edge_dn_crosses_iff_hp ex ey fx fy q ltac:(lra)) as [Hfwd _].
      exact (proj2 (Hfwd Hcr)). }
    exact (slice_x_contra outer hps q (mkPoint axx ayy, mkPoint bxx byy)
             (mkPoint ex ey, mkPoint fx fy) Hverts HeiHps (HinDec _ HedIn)
             ltac:(cbn [fst snd py]; lra) ltac:(cbn [fst snd py]; lra) Hstr_d Hsi Hsd).
Qed.

(* Corollary: the general exterior-even for y-unimodal convex rings. *)
Theorem convex_exterior_even_of_unimodal :
  forall (up down : list Point) (apex bottom : Point)
         (hps : list (R * R * R)) (q : Point) (outer : Ring),
    y_strict_incr (up ++ [apex]) ->
    y_strict_decr (apex :: down) ->
    (2 <= length (up ++ [apex]))%nat ->
    (2 <= length (apex :: down))%nat ->
    Forall (vertices_in_halfplane outer) hps ->
    Forall (fun e => In (edge_inward_hp e) hps) (ring_edges (up ++ [apex])) ->
    py (hd dpt (up ++ [apex])) = py bottom ->
    py (last (apex :: down) dpt) = py bottom ->
    last (up ++ [apex]) dpt = apex ->
    outer = up ++ apex :: down ->
    conv_min hps q < 0 ->
    (forall v, In v outer -> py v <> py q) ->
    ~ point_in_ring q outer.
Proof.
  intros up down apex bottom hps q outer Hinc Hdec Hleni Hlend Hverts HincHps
         Hhd Hlastd Hlasti Houter Hext Hav Hpir.
  assert (Hbs : bimonotone_split outer (ring_edges (up ++ [apex])) (ring_edges (apex :: down))).
  { rewrite Houter. apply bimonotone_split_unimodal; assumption. }
  pose proof (convex_exterior_balanced_of_unimodal up down apex bottom hps q outer
                Hinc Hdec Hleni Hlend Hverts HincHps Hhd Hlastd Hlasti Houter Hext Hav)
    as Hbal.
  apply (proj1 (bimonotone_split_parity outer _ _ q Hbs)) in Hpir.
  destruct Hpir as [[Hi Hnd] | [Hni Hd]].
  - exact (Hnd (proj1 Hbal Hi)).
  - exact (Hni (proj2 Hbal Hd)).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions convex_exterior_balanced_of_unimodal.
Print Assumptions convex_exterior_even_of_unimodal.
Print Assumptions convex_exterior_even_of_balanced.
Print Assumptions balanced_of_exterior_even.
Print Assumptions convex_offring_seam_of_balanced.
Print Assumptions diamond_exterior_balanced.
Print Assumptions hexagon_exterior_balanced.
