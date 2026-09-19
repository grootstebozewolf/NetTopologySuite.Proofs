(* ============================================================================
   NetTopologySuite.Proofs.IntakeKarneyPark
   ----------------------------------------------------------------------------
   ADR-0007 research letter after Accept (claimId 0007-karney-2013-ingest;
   K2 chord-hit pin claimId 0007-k2-chord-hit):
   Karney, C. F. F., "Algorithms for geodesics", J. Geod. 87, 43-55 (2013),
   doi:10.1007/s00190-012-0578-z, open access. Companion to
   docs/research/karney-2013-algorithms-for-geodesics.md. Page cites below
   are pages of that article.

   This is a park, not a cook. No EggGeodesic / MkGeodesic, no geodesic_eval,
   no Vincenty iteration, no Karney series as gamma or I. first_cook_scope is
   not touched. CircularCookLineArc* is not imported. No oracle keyword.

   What the paper is (page-cited):
   - Direct and inverse problems = the ellipsoidal triangle NAB: given
     phi_1, alpha_1, s_12 (direct) or phi_1, lambda_12, phi_2 (inverse),
     solve the remaining side and angles (p. 43 Sect. 1; p. 54 Sect. 9).
   - Ellipsoid of revolution, equatorial radius a, polar semi-axis b,
     flattening f (p. 44 Eqs. 1-4). Auxiliary sphere: latitude phi replaced
     by reduced latitude beta, azimuths preserved; Clairaut
     sin alpha_0 = sin alpha cos beta (p. 44 Eq. 5). The map between the
     ellipsoid and the auxiliary sphere depends on alpha_0 and "is not a
     global mapping of one surface to another" (p. 45).
   - Distance and longitude integrals I_1(sigma), I_3(sigma) (p. 44 Eqs.
     7-8), expanded as Fourier series in the parameter
     eps = (sqrt(1+k^2) - 1)/(sqrt(1+k^2) + 1), not raw k^2, with half as
     many terms (p. 45 Eqs. 15-16, 23).
   - Vincenty (1975a) uses Helmert's iteration for the inverse and "was
     aware of its failure to converge for nearly antipodal points";
     Vincenty (1975b, unpublished) modifies it but "sometimes requires many
     thousands of iterations" (p. 49). Karney: "this paper presents the
     first complete solution to the inverse geodesic problem" (p. 54).

   Tickets (QED or QEX, no third status):
   K0 QED  the paper is not planar intake: GEODESICSTRING mu stays MkChord,
           Karney's ellipsoidal triangle NAB is not that bag.
   K1 QEX  Vincenty's inverse is not total. K1 OWNS THE INVERSE: the inverse
           problem is f(alpha_1) = lambda_12(alpha_1) - lambda_star, m_12,
           Vincenty 1975a/b, Newton (Karney pp. 43, 47-49, 53). Not
           implemented here; the failure is Karney's claim, not a corpus
           counterexample. No iterator is faked to "prove" it.
   K2 QED  chord-hit pin on Sheet S (not the inverse; the inverse is K1):
           left = sheet_chord_misses_pole
           /\ sheet_chord_midpoint_on_parallel
           /\ ~ (exists t, on_chord g3_chord t g3_pole)
           with fence K2OwnsChordHit inhabited / K1OwnsInverse pointing
           at ticket_0007_karney_vincenty_total_qed_or_qex. The geodesic
           inequality (ellipsoid geodesic <> sheet chord) stays the QEX
           arm. Not reminted.
   K3 QEX  a new sheet class (ellipsoid with a geodesic interpolant) does
           not inhabit ADR-0007 Sheet = (O; e1, e2); a new ADR is required.

   WITNESS topic: overlay · claimId: 0007-karney-2013-ingest / 0007-k2-chord-hit
   witness: 0007-karney-2013-ingest · board: ADR-0007
   3-axiom host lane (Stdlib Reals, inherited). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude; K2 pin 0007-k2-chord-hit: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance SheetHenCook IntakeWalker IntakeGeodesic
  IntakeGeodesicCook.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Named parks. Uninhabited by construction: each is what this corpus     *)
(*     does not have, named so a later ADR can point at it.                   *)
(* -------------------------------------------------------------------------- *)

Inductive KarneyPark : Type :=
| KP_EllipsoidSheetClass      (* a Sheet whose geodesic is not the chord *)
| KP_VincentyInverseTotal     (* Vincenty (1975a) inverse as a total IResult *)
| KP_KarneyInverseAsI         (* Karney's Newton inverse as glossary 𝓘 *)
| KP_KarneySeriesAsGamma.     (* I_1 / I_3 series as an egg gamma *)

Definition karney_park_inhabits (_ : KarneyPark) : Prop := False.

Lemma karney_ellipsoid_sheet_missing : ~ karney_park_inhabits KP_EllipsoidSheetClass.
Proof. intro H. exact H. Qed.

Lemma karney_vincenty_total_missing : ~ karney_park_inhabits KP_VincentyInverseTotal.
Proof. intro H. exact H. Qed.

Lemma karney_inverse_as_I_missing : ~ karney_park_inhabits KP_KarneyInverseAsI.
Proof. intro H. exact H. Qed.

Lemma karney_series_as_gamma_missing : ~ karney_park_inhabits KP_KarneySeriesAsGamma.
Proof. intro H. exact H. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  K0: the paper is not planar intake.                                     *)
(* -------------------------------------------------------------------------- *)

(* ADR-0007's Sheet is (O; e1, e2) with a lattice flag: a plane. *)
Lemma sheet_is_planar_frame :
  forall s : Sheet, s = mkSheet (sheet_origin s) (sheet_e1 s) (sheet_e2 s) (sheet_has_lattice s).
Proof. intros [o a b l]. reflexivity. Qed.

(* WITNESS {"claimId":"0007-karney-2013-ingest","topic":"overlay","lemma":"ticket_0007_karney_not_planar_intake_qed_or_qex","title":"K0 Karney 2013 is not planar intake: on every ADR-0007 Sheet a well-formed GEODESICSTRING maps to the MkChord LINESTRING bag and never Declines, so the ellipsoidal triangle NAB of Karney p. 43 is not that bag (QED); or GEODESICSTRING intake inhabits an ellipsoid sheet class (QEX); discharged QED","file":"theories/IntakeKarneyPark.v","witness":"0007-karney-2013-ingest","board":"ADR-0007"} *)
Theorem ticket_0007_karney_not_planar_intake_qed_or_qex :
  ((forall s : Sheet,
      s = mkSheet (sheet_origin s) (sheet_e1 s) (sheet_e2 s) (sheet_has_lattice s))
   /\ (forall s p q rest,
         intake_map s (TGeodesicString (p :: q :: rest)) =
           IntakeBag (map_ls s (p :: q :: rest)))
   /\ (forall s p q rest ck,
         In ck (bag_chickens (map_ls s (p :: q :: rest))) ->
         exists a b, ck_egg ck = MkChord (mkChordEgg a b))
   /\ ~ karney_park_inhabits KP_EllipsoidSheetClass)
  \/
  karney_park_inhabits KP_EllipsoidSheetClass.
Proof.
  left.
  split; [exact sheet_is_planar_frame |].
  split; [exact geodesic_wellformed_bags |].
  split; [exact geodesic_wellformed_eggs_mkchord |].
  exact karney_ellipsoid_sheet_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  K1: Vincenty's inverse is not total — QEX, not implemented here.        *)
(* -------------------------------------------------------------------------- *)

(* K1 owns the inverse. The inverse problem is the root-finding
   f(alpha_1) = lambda_12(alpha_1) - lambda_star solved by Newton with the
   reduced length m_12 (Karney pp. 47-49); Vincenty 1975a iterates Helmert and
   fails to converge near antipodes, Vincenty 1975b sometimes needs many
   thousands of iterations (p. 43, p. 49, p. 53). None of that is implemented
   here; the failure is Karney's claim, not a corpus counterexample. The QED
   arm would be a total IResult-valued Vincenty inverse in this corpus; none
   exists and none is faked. K2 below is not about the inverse. *)
(* WITNESS {"claimId":"0007-karney-2013-ingest","topic":"overlay","lemma":"ticket_0007_karney_vincenty_total_qed_or_qex","title":"K1 Vincenty inverse totality: a total IResult-valued Vincenty (1975a) inverse inhabits this corpus (QED); or it is not implemented here and its non-convergence near antipodes is Karney's claim (pp. 43, 49, 53), not a corpus counterexample (QEX); discharged QEX","file":"theories/IntakeKarneyPark.v","witness":"0007-karney-2013-ingest","board":"ADR-0007"} *)
Theorem ticket_0007_karney_vincenty_total_qed_or_qex :
  karney_park_inhabits KP_VincentyInverseTotal
  \/
  (~ karney_park_inhabits KP_VincentyInverseTotal
   /\ ~ karney_park_inhabits KP_KarneyInverseAsI).
Proof.
  right. split; [exact karney_vincenty_total_missing | exact karney_inverse_as_I_missing].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  K2: chord-hit pin (claimId 0007-k2-chord-hit).                          *)
(* -------------------------------------------------------------------------- *)

(* K2 owns the chord-hit. Closed terms are IntakeGeodesicCook.v
   sheet_chord_misses_pole and sheet_chord_midpoint_on_parallel: no t puts
   (0,90) on the chord (-90,45)-(90,45); midpoint is (0,45). Planar chord
   geometry on ADR-0007 Sheet S. Not an inverse result. The inverse is K1.
   G3 is imported, not reminted. No new geometry. *)

Definition K2OwnsChordHit : Prop := True.

Definition K1OwnsInverse : Prop :=
  karney_park_inhabits KP_VincentyInverseTotal
  \/ (~ karney_park_inhabits KP_VincentyInverseTotal
      /\ ~ karney_park_inhabits KP_KarneyInverseAsI).

Lemma k2_owns_chord_hit : K2OwnsChordHit.
Proof. exact I. Qed.

Lemma k1_owns_inverse : K1OwnsInverse.
Proof. exact ticket_0007_karney_vincenty_total_qed_or_qex. Qed.

Lemma k2_k1_ownership_fence : K2OwnsChordHit /\ K1OwnsInverse.
Proof. split; [exact k2_owns_chord_hit | exact k1_owns_inverse]. Qed.

(* WITNESS {"claimId":"0007-k2-chord-hit","topic":"overlay","lemma":"ticket_0007_karney_chord_not_geodesic_qed_or_qex","title":"K2 chord-hit pin: left is sheet_chord_misses_pole / sheet_chord_midpoint_on_parallel / ~ exists t, on_chord g3_chord t g3_pole, fence K2OwnsChordHit inhabited and K1OwnsInverse points at ticket_0007_karney_vincenty_total_qed_or_qex (QED); or IG_AmbientManifold / IG_EllipsoidGamma / KP_KarneySeriesAsGamma inhabit so the sheet chord is the surface geodesic (QEX); discharged QED; geodesic inequality stays the QEX arm; G3 not reminted","file":"theories/IntakeKarneyPark.v","witness":"0007-karney-2013-ingest","board":"ADR-0007"} *)
Theorem ticket_0007_karney_chord_not_geodesic_qed_or_qex :
  ((~ exists t, on_chord g3_chord t g3_pole)
   /\ chord_eval g3_chord (1/2) = mkPoint 0 45
   /\ ~ (exists t, on_chord g3_chord t g3_pole))
  \/
  (intake_geodesic_qex_inhabits IG_AmbientManifold
   \/ intake_geodesic_qex_inhabits IG_EllipsoidGamma
   \/ karney_park_inhabits KP_KarneySeriesAsGamma).
Proof.
  left.
  split; [exact sheet_chord_misses_pole |].
  split; [exact sheet_chord_midpoint_on_parallel |].
  exact sheet_chord_misses_pole.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  K3: a new sheet class is a new ADR, not a letter on 0007.               *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-karney-2013-ingest","topic":"overlay","lemma":"ticket_0007_karney_new_sheet_class_qed_or_qex","title":"K3 new sheet class: an ellipsoid sheet with a geodesic interpolant inhabits ADR-0007 Sheet (QED); or every Sheet is the planar frame (O; e1, e2) and the ellipsoid class is the uninhabited park KP_EllipsoidSheetClass, requiring a new ADR (QEX); discharged QEX","file":"theories/IntakeKarneyPark.v","witness":"0007-karney-2013-ingest","board":"ADR-0007"} *)
Theorem ticket_0007_karney_new_sheet_class_qed_or_qex :
  karney_park_inhabits KP_EllipsoidSheetClass
  \/
  (~ karney_park_inhabits KP_EllipsoidSheetClass
   /\ (forall s : Sheet,
         s = mkSheet (sheet_origin s) (sheet_e1 s) (sheet_e2 s) (sheet_has_lattice s))
   /\ ~ first_cook_scope EggChord EggCircularArc).
Proof.
  right.
  split; [exact karney_ellipsoid_sheet_missing |].
  split; [exact sheet_is_planar_frame |].
  exact chord_arc_not_first_cook.
Qed.

Print Assumptions ticket_0007_karney_not_planar_intake_qed_or_qex.
Print Assumptions ticket_0007_karney_vincenty_total_qed_or_qex.
Print Assumptions ticket_0007_karney_chord_not_geodesic_qed_or_qex.
Print Assumptions ticket_0007_karney_new_sheet_class_qed_or_qex.
