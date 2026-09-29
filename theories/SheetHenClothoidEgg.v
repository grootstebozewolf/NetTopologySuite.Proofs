(* ============================================================================
   NetTopologySuite.Proofs.SheetHenClothoidEgg
   ----------------------------------------------------------------------------
   Host clothoid gamma. ISO/IEC 13249-3 ST_Clothoid (concept 4.2.11,
   type 7.8.1 rules 8-15, ST_StartPoint / ST_EndPoint 7.8.9 / 7.8.10)
   says the start and end points are calculated from the placement,
   the scale factor and the two distances, and does not print a
   formula. The parameterisation below is OUR choice, not an ISO
   formula. It is the oracle K token (oracle/driver.ml): one tangent
   at the inflection, scale A, distances sd and ed along the arc.

   Placement: origin LOCATION plus exactly two reference vectors
   (rule 12). Heading and position, with s the signed arc length from
   the inflection:
     phi(s) = phi0 + sigma * s^2 / (2 A^2)
     P(s)   = LOCATION + integral_0^s (cos phi(u), sin phi(u)) du
   phi0 is the direction of the first reference vector (its unit
   vector; no atan2). sigma is the sign of ref1 x ref2: +1 when the
   cross is nonnegative, otherwise -1. sigma = +1 is the oracle
   heading phi(s) = phi0 + s^2 / (2 A^2); the oracle token has no
   second vector, and the right-handed frame is that choice. The
   second vector is carried and used only for this handedness sign.
   Equivalent normalised form, sigma = +1 only:
     P = LOCATION + R(phi0) * A * sqrt(pi)
           * (C(s / (A * sqrt(pi))), S(s / (A * sqrt(pi))))
   where C and S are the Fresnel integrals of cos(pi t^2 / 2) and
   sin(pi t^2 / 2). Host eval is planar (rules 10-11, the 3D reading
   of the placement, are out of scope):
     gamma(t) = P(sd + t * (ed - sd)), t in [0,1].
   Rule 8: cloth_m0 and cloth_m1 are both None or both Some.
   Rule 9: the egg is measured exactly in the both-Some case.
   Endpoints are not stored. cloth_p0 / cloth_p1 are gamma(0) / gamma(1).
   Raw mkClothoidEgg cannot store a stale endpoint; cloth_wf is the
   constraint (A > 0, first vector nonzero, the two vectors not
   parallel, rule 8). Split is a sub-window of the same placement and
   A; child measures are None (a sub-arc does not inherit M).
   A = 0 is a total degenerate (Rinv 0 = 0), not well-formed.
   sd = ed is a constant gamma. The zero window sd = ed = 0 sits at
   LOCATION.

   CIRCLE-class intake exception: the example5 WKT seed was the chord
   (0,0)-(1,0). The locked bag is the law (parameterised WKT intake
   of arbitrary A, sd, ed is out of scope); its points are gamma ends
   of locked_clothoid_egg, not that chord seed.
   claimId: 0007-clothoid-first-cook / 0007-intake-mkclothoid
   WITNESS topic: overlay · board: ADR-0007.
   The integral is LipInt (3-axiom, no RiemannInt).
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

(* Module-split umbrella. Record and eval: SheetHenClothoidCore.
   Fresnel bounds: SheetHenClothoidBounds. Unit frames and the locked
   bag: SheetHenClothoidFrames. Importers keep this name. *)

From NTS.Proofs Require Export
  SheetHenClothoidCore SheetHenClothoidBounds SheetHenClothoidFrames.
