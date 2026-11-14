<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Spec #523 — `CURVE_RELATE_MATRIX` alphabet

**Type:** task · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** [Grill #523](12-grill-523-curve-relate-alphabet.md) · **Closed:** 2026-08-30 (spec written; ticket 523 stays open)

Living spec: [`docs/scout/spec-523.md`](../../spec-523.md).
Grill record: [`docs/scout/map-523.md`](../../map-523.md).

## Question

Turn the grilled #523 record into a takeable `/implement` spec: alphabet,
E/B refuse, exhausted-probe meaning, parks, and explicit non-goals.
Do not implement the driver rewrite. Do not accept ticket 523. Do not
mint leftover `Ⅲ`.

## Resolution

**Closed 2026-08-30 with the spec written.** Ticket 523 stays open and
is not accepted. Ticket 11 precondition 3 is still “resolved or
explicitly accepted.”

Delivered:

- [`spec-523.md`](../../spec-523.md) — three grilled asks as acceptance
  criteria; slices A (E/B `failwith`) / B (consumers learn `?` as a
  matrix cell) / C (driver emits `?`); parks per ADR-0002.
- Pointers from the grill map, ticket 11, this README, and the
  `RelateCurveMatrix.v` claims row.
- Later cut into `523-a` / `523-b` / `523-c` (ticket 14).

`?` is the issue’s proposed wire glyph, not a CONTEXT term. Whole-
matrix Decline stays `UNSUPPORTED`
(`RelateNGCore.v : relate_unsupported_no_predicate`). Per-cell unknown
is not Decline. Do not steal `UNSUPPORTED` as a cell.

Do **not** implement those slices here. Do **not** mint leftover
`Ⅲ`. Do **not** remint classifier pins.
