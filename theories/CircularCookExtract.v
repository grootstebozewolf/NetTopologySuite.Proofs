(* ============================================================================
   NetTopologySuite.Proofs.CircularCookExtract
   ----------------------------------------------------------------------------
   Host-lane extraction of I_circles_z (OCaml int Z). Official pin is
   Validate_binary64_extract (inductive Z). Not trusted.

   Not compiled by `_CoqProject` / `_CoqProject.full` — run:

     rocq c -Q theories NTS.Proofs theories/CircularCookExtract.v

   from the repo root after CircularCookZ.vo exists.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
From NTS.Proofs Require Import CircularCookZ.

Extraction Language OCaml.
Extraction "oracle/circular_cook_extracted.ml" I_circles_z hen_plus hen_minus.
