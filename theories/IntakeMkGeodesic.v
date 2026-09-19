(* ============================================================================
   NetTopologySuite.Proofs.IntakeMkGeodesic
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept (claimId 0007-mk-geodesic). Host Egg
   constructor hole only. Distinct from GeodesicGammaOnSheet (#803
   interpolant g : [0,1] → S) and from sidecar GeodesicMkGeodesic
   (claimId 0007-geodesicstring-egg).

   On ADR-0007 Sheet S = (O; e1, e2) GEODESICSTRING μ is MkChord (K0).
   Egg has no MkGeodesic. There is no host interpolant other than that
   chord. sheet_chord_misses_pole is chord-hit, not g. Inverse is K1.
   K2 owns pole-on-chord. A non-chord geodesic needs a non-planar sheet
   class (K3 / ADR-0008). Do not fake MkGeodesic := MkChord.

   QED arm (all must hold; they do not on planar S): MkGeodesic :
   GeodesicEgg → Egg with egg_class EggGeodesicString; on_geodesic is
   not on_chord on a locked fixture; first_cook_scope
   EggGeodesicString EggGeodesicString only after that; mixed
   geodesic×chord stays Decline; GeodesicGammaOnSheet inhabits as that
   interpolant, not a rename of MkChord; ADR-0008 Accepted only if
   E0–E4 inhabit in this same letter.

   QEX arm (this letter): do not add MkGeodesic; do not flip
   first_cook_scope EggGeodesicString; name MkGeodesic; keep
   GeodesicGammaOnSheet missing (#803); cite K0; ADR-0008 stays
   Proposed.

   WITNESS topic: overlay · claimId: 0007-mk-geodesic
   witness: 0007-mk-geodesic · board: ADR-0007
   3-axiom host lane (Stdlib Reals, inherited). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance SheetHenCook IntakeWalker IntakeGeodesic
  IntakeGeodesicCook IntakeKarneyPark.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Named missing constructor. The Egg hole, not #803's interpolant g.         *)
(* -------------------------------------------------------------------------- *)

Inductive MkGeodesicCtor : Type :=
| MkGeodesic.

Definition mk_geodesic_ctor_inhabits (_ : MkGeodesicCtor) : Prop := False.

Lemma mk_geodesic_missing :
  ~ mk_geodesic_ctor_inhabits MkGeodesic.
Proof. intro H. exact H. Qed.

(* Egg remains MkChord | MkCirc | MkClothoid | MkOutOfScope. Cited, not reminted. *)
Lemma mk_geodesic_egg_has_no_ctor :
  forall e : Egg,
    (exists c, e = MkChord c) \/ (exists g, e = MkCirc g) \/
    (exists k, e = MkClothoid k) \/ (exists cls, e = MkOutOfScope cls).
Proof. exact egg_no_mkgeodesic. Qed.

(* K0 μ = MkChord on planar S. Cited, not reminted as a geodesic. *)
Lemma mk_geodesic_k0_mu_mkchord :
  (forall s : Sheet,
     s = mkSheet (sheet_origin s) (sheet_e1 s) (sheet_e2 s) (sheet_has_lattice s))
  /\ (forall s p q rest ck,
        In ck (bag_chickens (map_ls s (p :: q :: rest))) ->
        exists a b, ck_egg ck = MkChord (mkChordEgg a b)).
Proof.
  split; [exact sheet_is_planar_frame | exact geodesic_wellformed_eggs_mkchord].
Qed.

(* GeodesicGammaOnSheet stays missing: no g, closed term is chord-hit. *)
Lemma mk_geodesic_gamma_stays_missing :
  ~ intake_geodesic_qex_inhabits IG_EllipsoidGamma
  /\ ~ (exists t, on_chord g3_chord t g3_pole).
Proof.
  split; [exact intake_geodesic_ellipsoid_missing | exact sheet_chord_misses_pole].
Qed.

Lemma mk_geodesic_no_first_cook :
  ~ first_cook_scope EggGeodesicString EggGeodesicString
  /\ ~ first_cook_scope EggChord EggCircularArc.
Proof.
  split; [intro H; exact H | exact chord_arc_not_first_cook].
Qed.

(* WITNESS {"claimId":"0007-mk-geodesic","topic":"overlay","lemma":"ticket_0007_mk_geodesic_qed_or_qex","title":"Host Egg MkGeodesic: MkGeodesic : GeodesicEgg to Egg inhabits with egg_class EggGeodesicString and on_geodesic not on_chord (QED); or MkGeodesic is the missing Egg ctor distinct from GeodesicGammaOnSheet (#803 interpolant g), K0 mu stays MkChord on planar S, first_cook_scope EggGeodesicString stays false, ADR-0008 stays Proposed (QEX); discharged QEX; MkGeodesic := MkChord is QEX not QED","file":"theories/IntakeMkGeodesic.v","witness":"0007-mk-geodesic","board":"ADR-0007"} *)
Theorem ticket_0007_mk_geodesic_qed_or_qex :
  mk_geodesic_ctor_inhabits MkGeodesic
  \/
  (~ mk_geodesic_ctor_inhabits MkGeodesic
   /\ (forall e : Egg,
         (exists c, e = MkChord c) \/ (exists g, e = MkCirc g) \/
         (exists k, e = MkClothoid k) \/ (exists cls, e = MkOutOfScope cls))
   /\ (forall s : Sheet,
         s = mkSheet (sheet_origin s) (sheet_e1 s) (sheet_e2 s) (sheet_has_lattice s))
   /\ (forall s p q rest ck,
         In ck (bag_chickens (map_ls s (p :: q :: rest))) ->
         exists a b, ck_egg ck = MkChord (mkChordEgg a b))
   /\ ~ intake_geodesic_qex_inhabits IG_EllipsoidGamma
   /\ ~ (exists t, on_chord g3_chord t g3_pole)
   /\ ~ karney_park_inhabits KP_EllipsoidSheetClass
   /\ ~ karney_park_inhabits KP_VincentyInverseTotal
   /\ ~ first_cook_scope EggGeodesicString EggGeodesicString
   /\ ~ first_cook_scope EggChord EggCircularArc).
Proof.
  right.
  split; [exact mk_geodesic_missing |].
  split; [exact egg_no_mkgeodesic |].
  split; [exact sheet_is_planar_frame |].
  split; [exact geodesic_wellformed_eggs_mkchord |].
  split; [exact intake_geodesic_ellipsoid_missing |].
  split; [exact sheet_chord_misses_pole |].
  split; [exact karney_ellipsoid_sheet_missing |].
  split; [exact karney_vincenty_total_missing |].
  split; [intro H; exact H |].
  exact chord_arc_not_first_cook.
Qed.

Print Assumptions ticket_0007_mk_geodesic_qed_or_qex.
Print Assumptions mk_geodesic_missing.
Print Assumptions mk_geodesic_egg_has_no_ctor.
Print Assumptions mk_geodesic_k0_mu_mkchord.
Print Assumptions mk_geodesic_gamma_stays_missing.
Print Assumptions mk_geodesic_no_first_cook.
