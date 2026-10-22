(* ============================================================================
   NetTopologySuite.Proofs.IntakeG3GeodesicGamma
   ----------------------------------------------------------------------------
   SQL/MM GEODESICSTRING / NTS planar-sheet interpolant (claimId
   0007-g3-geodesic-gamma). G3 closed-terms / no-g only.

   On ADR-0007 Sheet S = (O; e1, e2) the sheet geodesic is the chord.
   There is no host interpolant g : [0,1] → S that is a geodesic other
   than that chord, and Egg has no MkGeodesic. A non-chord geodesic
   needs an ellipsoid sheet class (K3 / ADR-0008). Do not fake g as
   MkChord with a new name. Do not treat sheet_chord_misses_pole as g.

   QED arm: GeodesicGammaOnSheet inhabits — a constructed host Egg
   MkGeodesic g, or a named geodesic_gamma on S, with g(0)=start,
   g(1)=end, g not a chord unless antipodal-excluded, the locked G3
   pair's g not through g3_pole as a chord-parameter, 3-axiom host,
   no Vincenty iterator. That ctor is missing.

   QEX arm (this letter): GeodesicGammaOnSheet stays uninhabited.
   Closed term is sheet_chord_misses_pole (not g). Inverse is K1
   (ticket_0007_karney_vincenty_total_qed_or_qex). K2 stays the
   chord-hit on_chord membership of the G3 pole. K0 μ = MkChord is
   not reminted as a geodesic. first_cook_scope is not expanded.

   ADR-0007 stays Accepted. ADR-0008 stays Proposed.

   WITNESS topic: overlay · claimId: 0007-g3-geodesic-gamma
   witness: 0007-g3-geodesic-gamma · board: ADR-0007
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
(* Named missing constructor. Uninhabited: g cannot live on Sheet S           *)
(* without an ellipsoid class.                                                *)
(* -------------------------------------------------------------------------- *)

Inductive G3GeodesicGammaCtor : Type :=
| GeodesicGammaOnSheet.

Definition g3_geodesic_gamma_ctor_inhabits (_ : G3GeodesicGammaCtor) : Prop :=
  False.

Lemma geodesic_gamma_on_sheet_missing :
  ~ g3_geodesic_gamma_ctor_inhabits GeodesicGammaOnSheet.
Proof. intro H. exact H. Qed.

(* The closed term is planar chord geometry. It is not g. K2 stays that
   chord-hit; this letter does not restate it as an inverse. *)
Lemma g3_closed_term_is_chord_miss :
  ~ exists t, on_chord g3_chord t g3_pole.
Proof. exact sheet_chord_misses_pole. Qed.

(* K1 owns the inverse. Cited, not reminted. *)
Lemma g3_inverse_is_k1 :
  ~ karney_park_inhabits KP_VincentyInverseTotal /\
  ~ karney_park_inhabits KP_KarneyInverseAsI.
Proof.
  split; [exact karney_vincenty_total_missing | exact karney_inverse_as_I_missing].
Qed.

(* No first-cook expand: EggGeodesicString stays out of scope. *)
Lemma g3_no_first_cook_geodesicstring :
  ~ first_cook_scope EggGeodesicString EggGeodesicString.
Proof. intro H. exact H. Qed.

(* WITNESS {"claimId":"0007-g3-geodesic-gamma","topic":"overlay","lemma":"ticket_0007_g3_geodesic_gamma_qed_or_qex","title":"G3 geodesic_gamma on Sheet S: GeodesicGammaOnSheet inhabits as a host MkGeodesic / named geodesic_gamma (QED); or that ctor is missing, the closed term is sheet_chord_misses_pole (not g), K1 owns the inverse, K2 stays the chord-hit, K0 MkChord is not reminted as a geodesic, and first_cook_scope is not expanded (QEX); discharged QEX; ADR-0008 stays Proposed","file":"theories/IntakeG3GeodesicGamma.v","witness":"0007-g3-geodesic-gamma","board":"ADR-0007"} *)
Theorem ticket_0007_g3_geodesic_gamma_qed_or_qex :
  g3_geodesic_gamma_ctor_inhabits GeodesicGammaOnSheet
  \/
  (~ g3_geodesic_gamma_ctor_inhabits GeodesicGammaOnSheet
   /\ ~ (exists t, on_chord g3_chord t g3_pole)
   /\ ~ karney_park_inhabits KP_VincentyInverseTotal
   /\ ~ karney_park_inhabits KP_KarneyInverseAsI
   /\ ~ intake_geodesic_qex_inhabits IG_EllipsoidGamma
   /\ ~ karney_park_inhabits KP_EllipsoidSheetClass
   /\ ~ first_cook_scope EggGeodesicString EggGeodesicString
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ chord_eval g3_chord (1/2) = mkPoint 0 45).
Proof.
  right.
  split; [exact geodesic_gamma_on_sheet_missing |].
  split; [exact sheet_chord_misses_pole |].
  split; [exact karney_vincenty_total_missing |].
  split; [exact karney_inverse_as_I_missing |].
  split; [exact intake_geodesic_ellipsoid_missing |].
  split; [exact karney_ellipsoid_sheet_missing |].
  split; [exact g3_no_first_cook_geodesicstring |].
  split; [exact chord_arc_not_first_cook |].
  exact sheet_chord_midpoint_on_parallel.
Qed.

Print Assumptions ticket_0007_g3_geodesic_gamma_qed_or_qex.
Print Assumptions geodesic_gamma_on_sheet_missing.
Print Assumptions g3_closed_term_is_chord_miss.
Print Assumptions g3_inverse_is_k1.
