<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Grill leftover `Ⅳ` — interior-side stem

**Type:** grilling · **Map:** [#522 leftovers](../../map-522-leftovers.md)
**Blocked by:** — · **Closed:** 2026-08-30 (grill written; leftover `Ⅳ` stays open)
**claimId:** `Ⅳ` · **GitHub:** none · **witness:** none

Living record: [`docs/scout/map-interior-side-grill.md`](../../map-interior-side-grill.md).
Research chart: [`docs/scout/map-interior-side-cert.md`](../../map-interior-side-cert.md) (#629).
Spec (later, ticket 24): [`docs/scout/spec-interior-side.md`](../../spec-interior-side.md).

## Question

Does leftover `Ⅳ` hold against the leftover-`Ⅲ` compile and against
CONTEXT? Name what holds. Park what does not. Do not invent a
12-tuple. Do not invent a side-distinguishing detector. Do not remint
`RelateNGCore.v : touch_onesided_t_b`. Do not restage #609 / #611 /
#628 / #629.

## Resolution

**Closed 2026-08-30 with the grill written.** CONTEXT Bar 1 is
not applicable (no leftover-`Ⅳ` matrix). Ticket 26 later compiled
the residue pair; this ticket does not.

Satisfied at grill time (verify then cite):

- The compiled onesided pair then was leftover `Ⅲ`
  (`RelateNGComplete.v : onesided_t_pair_inhabits`;
  `RelateNGComplete.v : onesided_t_ii_empty`).
- The xor is `Ⅲ∨Ⅳ`
  (`RelateNGCore.v : touch_onesided_t_b`;
  `RelateNGTouchOnesided.v : triangle_pair_regime_onesided`).
- `overlap_b` may steal same-side stems
  (`RelateNGCore.v : overlap_b`).
- Completeness stays false
  (`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`).

**Later (ticket 26).** Residue pair compiled:
`RelateNGComplete.v : interior_side_pair_inhabits`. Living grill
tense is the compile letter
([`map-interior-side-grill.md`](../../map-interior-side-grill.md)).
Do **not** mint `522-n`. Do **not** mint `Ⅴ`. Do **not** steal
leftover `Ⅰ` / `Ⅱ` / `Ⅲ`.
