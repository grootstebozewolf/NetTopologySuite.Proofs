(* ============================================================================
   NetTopologySuite.Proofs.Flocq.InCircle_b64_compute
   ----------------------------------------------------------------------------
   COMPUTATIONAL (extractable) binary64 in-circle determinant -- the oracle
   compute path for the RocqRefRunner INCIRCLE_SIGN mode (and the incircle
   sign-products inside the ARC_* modes).

   Mirrors `inCircle_R` (theories/ArcOrient.v:88) operation-for-operation on
   the `b64_*` layer, replacing the driver's hand-rolled `incircle_r_native`.
   `inCircle_R` is R-side (it lives on `Point`/`R`), so it is not directly
   extractable; this is its binary64 evaluator.

   Cofactor expansion along the first column of the 3x3 lifted determinant
   (translating P to the origin):
     ax := xA-xP  ay := yA-yP   bx := xB-xP  by := yB-yP   cx := xC-xP  cy := yC-yP
     na := ax^2+ay^2   nb := bx^2+by^2   nc := cx^2+cy^2
     ax*(by*nc - cy*nb) - ay*(bx*nc - cx*nb) + na*(bx*cy - cx*by).
   Positive iff (A,B,C) is CCW AND P is strictly inside the circumcircle.

   SOUNDNESS STATUS.  Deferred (docs/oracle-handroll-migration.md item 2).
   Unlike the Liang-Barsky filter, this determinant uses NO division, so in
   the integer regime |coord| <= 2^12 every +/-/* is exact (4k+2 <= 53) and
   the binary64 sign EQUALS `inCircle_R`'s sign -- a clean integer-regime
   exactness theorem (cf. Orient_b64_exact's `_sound_small_int`), not a
   forward-error bound.  Proving it is multi-session Flocq work; this file
   only provides the de-hand-rolled, single-sourced compute path (bit-exact
   with the previous native kernel via the usual Bplus->( +. ) overrides).
   ========================================================================== *)

From Flocq Require Import IEEE754.Binary.
From NTS.Proofs.Flocq Require Import Validate_binary64.

Definition b64_inCircle (A B C P : BPoint) : binary64 :=
  let ax := b64_minus (bx A) (bx P) in
  let ay := b64_minus (by_ A) (by_ P) in
  let bbx := b64_minus (bx B) (bx P) in
  let bby := b64_minus (by_ B) (by_ P) in
  let ccx := b64_minus (bx C) (bx P) in
  let ccy := b64_minus (by_ C) (by_ P) in
  let na := b64_plus (b64_mult ax ax) (b64_mult ay ay) in
  let nb := b64_plus (b64_mult bbx bbx) (b64_mult bby bby) in
  let nc := b64_plus (b64_mult ccx ccx) (b64_mult ccy ccy) in
  b64_plus
    (b64_minus
       (b64_mult ax (b64_minus (b64_mult bby nc) (b64_mult ccy nb)))
       (b64_mult ay (b64_minus (b64_mult bbx nc) (b64_mult ccx nb))))
    (b64_mult na (b64_minus (b64_mult bbx ccy) (b64_mult ccx bby))).
