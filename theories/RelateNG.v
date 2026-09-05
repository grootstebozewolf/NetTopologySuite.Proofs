(* ============================================================================
   NetTopologySuite.Proofs.RelateNG
   ----------------------------------------------------------------------------
   Issue #67 S13: full RelateNG pipeline integration — re-export umbrella.

   The former 1 750-line monolith was split (2026-08) into layered
   modules; this file re-exports them all, so existing
   `Require Import RelateNG` clients (RelatePrepared.v) are unaffected.
   The original section banners are preserved inside the split files, and
   the meso-audit B6 untangle (rect and triangle lanes were interleaved:
   `rect_pair_regime` sat inside the triangle block) is executed by the
   Core layout.  Layer map:

     - RelateNGCore.v        strata + rect/triangle regime classifiers +
         the top-level `relate` dispatch (`rect_geometry_bounds`,
         `rect_pair_regime`, `rects_relate`; `triangle_geometry`,
         `triangle_pair_regime`, `tris_relate`; `relate` + fidelity
         lemmas and the line fallback).
     - RelateNGContains.v    TPR_Contains regime correctness
         (`triangle_pair_regime_contains`; whole-boundary containment
         `contains_b_ring_inside` / `contains_b_ring_strictly_inside`
         via TriangleContainmentConvex).
     - RelateNGContainsBridge.v  #567 / 522-a detector→predicate bridge
         (`contains_b_ccw_implies_closed_containment`): `contains_b`
         plus B CCW lifts to closed `triangle_a_contains_b`.  Honesty
         pin: `contains_b` alone is not enough (CW-listed B).
     - RelateNGOverlap.v     TPR_Overlap regime at bar 1 (#570 / 522-b)
         (`triangle_pair_regime_overlap`; soundness
         `overlap_b_partial_overlap` via a centroid nudge).
     - RelateNGDisjoint.v    TPR_Disjoint regime at bar 1 (#571 / 522-c)
         (`triangle_pair_regime_disjoint`; soundness
         `separated_b_triangles_separated` via a supporting edge).
     - RelateNGTouchVertex.v TPR_TouchVertex regime at bar 1 (#572 / 522-i)
         (umbrella over RelateNGTouchVertexCone + RelateNGTouchVertexRegime;
         `triangle_pair_regime_touchvertex`; soundness
         `touch_vertex_b_triangles_touch` via a line through the
         shared vertex).  Expected re-export blast (hub, not extra
         leaf fan-out).  Leftover declines are #577 / 522-j.
     - RelateNGComplete.v    leftover-decline finding (#577 / 522-j):
         completeness is still FALSE (unnamed CCW pair).
         The compiled T-junction pair is leftover `Ⅰ` (classified).
         Leftover `Ⅱ` classifies obtuse-at-v. Leftover `Ⅴ`
         classifies mixed-cone.
     - RelateNGTouchPartialEdge.v leftover `Ⅰ` bar 1: mutual
         open-edge detector `touch_partial_edge_b` reaches
         `TPR_TouchPartialEdge` (fill stays `im_unsupported`).
     - RelateNGTouchOnesided.v leftover `Ⅲ` exterior-side stem and
         leftover `Ⅳ` interior-side stem: `Ⅲ∨Ⅳ` xor
         `touch_onesided_t_b` reaches `TPR_TouchOnesided` on both
         compiled witnesses (fill stays `im_unsupported`; not
         CONTEXT Bar 1).
     - RelateNGTouchObtuse.v leftover `Ⅱ`: closed-cone detector
         `touch_obtuse_vertex_b` reaches `TPR_TouchObtuse`
         (fill stays `im_unsupported`; not CONTEXT Bar 1).
         #577 stop is QED ∨ QEX (`triangle_pair_regime_ccw_stop`);
         leftover `Ⅱ` is QED. Completeness is unnamed after
         leftover `Ⅴ`.
     - RelateNGTouchMixedCone.v leftover `Ⅴ`: opposite-sign cone
         detector `mixed_cone_vertex_b` reaches `TPR_MixedCone`
         (fill stays `im_unsupported`; not CONTEXT Bar 1).
         Leftover `Ⅴ` is QED.
     - RelateNGTouchSameCone.v leftover `Ⅵ`: same-sign cone
         detector `same_cone_vertex_b` reaches `TPR_SameCone`
         (fill stays `im_unsupported`; not CONTEXT Bar 1).
         Leftover `Ⅵ` is QED. Completeness is an unnamed lens
         pair (not leftover `Ⅶ`).
     - RelateNGRingInclusion.v  half-open ring-inclusion groundwork
         (#568 / 522-g): a strict-`gtri` point has an explicit open
         disk of strict points; a nondegenerate segment carries dim-1;
         the #530 sentinel IE cell has dim-2 content.  Does not remint
         `aa_matrix_disjoint` (empty IE is #573 / 522-d).
     - RelateNGDisjointCells.v  #573 / 522-d: nine gtri cells of
         OGC FF2FF1212 on the #571 sentinel (`sentinel_disjoint_ogc_gtri_cells`).
         Names `aa_matrix_disjoint_ogc`; Qex `~ im_disjoint` of that fill
         (`pat_disjoint` forces EI=EB=F).  Does not remint
         `aa_matrix_disjoint` or `triangle_pair_fill`.
     - RelateNGContainsCells.v  #576 / 522-h (contains split): nine
         gtri cells of OGC 212FF1FF2 on the #567 contains pair
         (`contains_pair_ogc_gtri_cells`).  Names `aa_matrix_contains_ogc`;
         Qex: classifier IB is empty while IB is dim-1.  Does not remint
         `aa_matrix_contains` or `triangle_pair_fill`.
     - RelateNGTouchEdgeCells.v  #576 / 522-h (touch-edge split): nine
         gtri cells of OGC FF2F11212 on the frozen shared-edge pair
         (`touch_edge_pair_ogc_gtri_cells`).  Names
         `aa_matrix_touch_edge_ogc`; Qex: classifier IE is empty while
         IE is dim-2.  Does not remint `aa_matrix_touch_vertical` or
         `triangle_pair_fill`.
     - RelateNGOverlapCells.v  #576 / 522-h (overlap split): nine
         gtri cells of OGC 212101212 on the #567 / #570 overlap pair
         (`overlap_pair_ogc_gtri_cells`).  Names `aa_matrix_overlap_ogc`;
         Qex: classifier IE is empty while IE is dim-2.  Does not remint
         `aa_matrix_partial_overlap` or `triangle_pair_fill`.
     - RelateNGOracleSurface.v  #575 / 522-f: oracle wire token
         (`triangle_unsupported_token`): a decline is
         `RWR_Unsupported`, not a 9-cell matrix.  Classified triangle
         fills pin as they stand (FFFFFFFFF / 2FFF1FFF2 / 2FFFFFFF2 /
         FFFF1FFF2).  `relate` of the T-junction is the token
         (`relate_tjunction_wire_unsupported`); Qex: the #530 pair
         is a disjoint matrix, not UNSUPPORTED.  Does not remint
         `aa_matrix_disjoint`.
     - RelateNGTouch.v       shared-edge touch regime
         (`triangles_touch_on_shared_edge` + detector agreement
         `triangle_pair_regime_touch`; strict interior separation
         `touch_triangle_pair_strict_ii_no_common`;
         `touch_int_ext_exclusion{,_weak}`; `relate_triangle_touch`).
     - RelateNGTouchRED.v    RED refutation: the parity SInt sets of two
         CCW shared-edge triangles overlap at the vertex-grazing
         p = (-1,1), so guard-free II separation is FALSE
         (`touch_triangle_ii_separation_not_unconditional`).
     - RelateNGTouchCells.v  DE-9IM cells for the touch regime: EE/II/BB
         cells, the JCT seam lift
         (`point_set_characterises_geometric_interior`), the guarded II
         cell via the seam, the unconditional geometric-interior
         separation, and the capstones
         (`touch_triangles_regime_cells_ii_bb_ee`).
     - RelateNGRect.v        rect regime cells + dispatch fidelity
         (touch pins, `relate_on_rects_dispatches`, overlap fill facts,
         `touch_rect_pair_{ee,ii}_cell`, BB point constructor, examples).

   Provides (unchanged public surface): the top-level relate computation and
   matrix assembly, integrating the MOD2 boundary policy (RelateBoundary),
   the area-line / area-area regime cases + general strata, dim assignment
   with Jordan soundness hooks, and the prepared cache wrapper (delegates to
   RelatePrepared).

   No `Admitted`, no `Axiom`, no `Parameter`.  Per-theorem audit footprints
   (`Print Assumptions`) live in the split files, next to their theorems.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From NTS.Proofs Require Export
  RelateNGCore
  RelateNGContains
  RelateNGContainsBridge
  RelateNGOverlap
  RelateNGDisjoint
  RelateNGTouchVertex
  RelateNGTouch
  RelateNGTouchRED
  RelateNGTouchCells
  RelateNGRect
  RelateNGComplete
  RelateNGTouchPartialEdge
  RelateNGTouchOnesided
  RelateNGRingInclusion
  RelateNGDisjointCells
  RelateNGContainsCells
  RelateNGTouchEdgeCells
  RelateNGOverlapCells
  RelateNGOracleSurface.
