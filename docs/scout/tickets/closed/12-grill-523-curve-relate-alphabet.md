<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Grill #523 — `CURVE_RELATE_MATRIX` alphabet

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** — · **Closed:** 2026-08-30 (decision: **do not** resolve ticket 523; **do not** accept)

Living record: [`docs/scout/map-523.md`](../../map-523.md).
Spec (later, ticket 13): [`docs/scout/spec-523.md`](../../spec-523.md).

## Question

Does #523 still hold against the tree? Accept as documented, split, or
keep open? Ticket 11 precondition 3 waits on “resolved or explicitly
accepted.”

## Resolution

**Closed 2026-08-30 with the decision that ticket 523 does not resolve
and is not accepted.** The three F-without-empty claims are live.
Line numbers in the issue body have drifted; the facts have not. Cite
[`map-523.md`](../../map-523.md).

Satisfied (verify then cite):

- Lineal E/B `pair_pts` returns `[]` (`oracle/driver.ml:3983`). Empty
  contact prints `"FFFFFFFFF"`.
- Header still says “others F” (`:3801`). Areal miss → `-1` → `'F'`
  (`:4368`).
- Open cells are an 80×80 grid (`:4332`). Miss is not
  `RelateCurveMatrix.v : cell_none_iff_empty`.
- EE is the established exception:
  `RelateCurveMatrix.v : geom_de9im_ee_nonempty`.
- Whole-matrix Decline is already honest
  (`RelateNGCore.v : relate_unsupported_no_predicate`). Per-cell
  unknown is not Decline. CONTEXT has no name for it; this grill does
  not invent one.
- Buffer modes still `failwith` on `E`/`B` (`BUFFER_REGION:3353`,
  `BUFFER_UNIFIED:3482`).

Residue that stays on ticket 523 (sequencing park, ADR-0002):

1. Alphabet: `F` only where emptiness is established.
2. Elliptic / Bézier refuse (not `[]`, not centre/chord proxy).
3. Name what a not-computed token from an exhausted probe means, once
   that token exists.

Do **not** implement those here. Do **not** mint leftover `Ⅲ`.
Do **not** remint classifier pins. Ticket 11 precondition 3 remains
unmet.
