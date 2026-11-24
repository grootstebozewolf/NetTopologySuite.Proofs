(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLine
   ----------------------------------------------------------------------------
   Issue #67 sessions 15a–15k (S15a–S15k): line×line point-set DE-9IM bridge —
   re-export umbrella.

   The former 2 500-line monolith was split (2026-08) into layered
   modules; this file re-exports them all, so existing
   `Require Import RelateNodingLineLine` clients (RelateEdgeNodeStratum,
   RelateEdgeNodeDecide, RelateEdgeDisjointCert) are unaffected.  The
   original §1–§20 section numbers are preserved inside the split files, so
   the S15 session retros (docs/history/sessions/issue-67-s15*-retro.md)
   remain accurate.  Layer map:

     - RelateNodingLineLineStrata.v      §1–§3, §13  (S15a)
         `LineStratum` + `seg_in_stratum` / `line_cell_ok` /
         `line_de9im_pointset`; `two_segments_exterior_meet`;
         `line_de9im_matrix_ok`.
     - RelateNodingLineLineMeet.v        §4–§10      (S15a–S15g)
         per-regime meet-cell bridges (disjoint, proper cross, collinear
         overlap incl. degenerate `C = D` and shared-endpoint BB,
         interior share, T-junction Touches contact).
     - RelateNodingLineLineRows.v        §11–§12, §16 (S15c–S15h)
         Romanschek EE = 2 row; OGC exterior rows (IE/EI/BE/EB); JTS#1175
         nominated-pair BI negative; per-pair test-10 fill bridges.
     - RelateNodingLineLineCollection.v  §14–§15, §17–§18 (S15f–S15i)
         JTS#1175 collection BI witness; collection union semantics;
         `dim_value_join` / `matrix_dim_join` max cell algebra; cross-
         product fold soundness; test-10 collection pointset.
     - RelateNodingLineLinePinned.v      §19         (S15j)
         `line_cell_true_dim` / `line_cell_ok_pinned` + II/BB regime pins.
     - RelateNodingLineLineExtPinned.v   S15l / 67-c
         exterior-row true-dimension pinning (IE/EI/BE/EB/EE) +
         `line_pair_fill_disjoint_ie_not_true_dim` fill-honesty gap.
     - RelateNodingLineLineTouches.v     S15l+ / 67-d
         `LPR_Touches` fill (`ll_matrix_touches_endpoint`) for int×bnd
         contact.  `LPR_Share` stays the point-II matrix.
     - RelateNodingLineLineCapstone.v    §20         (S15k)
         collection relate-matrix pipeline capstone (fold-assign + regime
         wrapper + test-10 pointset / fold=oracle / intersects).

   Honest gaps (remaining S15l+):

     - Prepared evaluate hook (identity `prepared_evaluate_agrees` already
       Qed; end-to-end cache-path still the S13–S14 skeleton).
     - Touches-vs-Share fill split landed as `LPR_Touches` (67-d).
       Multi-geom and the nine-cell `geom_de9im_pointset` capstone remain.

   No `Admitted`, no `Axiom`, no `Parameter`.  Per-theorem audit footprints
   (`Print Assumptions`) live in the split files, next to their theorems.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From NTS.Proofs Require Export
  RelateNodingLineLineStrata
  RelateNodingLineLineMeet
  RelateNodingLineLineRows
  RelateNodingLineLineCollection
  RelateNodingLineLinePinned
  RelateNodingLineLineExtPinned
  RelateNodingLineLineTouches
  RelateNodingLineLineCapstone.
