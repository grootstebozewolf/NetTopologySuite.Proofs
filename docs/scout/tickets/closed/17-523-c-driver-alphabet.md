<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# `523-c` — `CURVE_RELATE_MATRIX` prints `?` where it did not compute

**Type:** task · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** [`523-b` / #604](16-523-b-cell-unknown.md) · **Spec:** [`spec-523.md`](../../spec-523.md) slice C
**claimId:** `523-c` · **GitHub:** [#605](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/605) · **witness:** `523-c-driver-unknown`

> Umbrella: ticket 523 / #605. Does not retire that issue. Not leftover `Ⅲ`.
> Gate: `523-b` / #604 must land first so consumers do not reject the new
> cell glyph.

## Question

The oracle prints `F` for lineal undistinguished cells and for an
80×80 areal grid miss. Those are not Coq `None`
(`RelateCurveMatrix.v : cell_none_iff_empty`). Print `?` there.
Keep `F` only where emptiness is established. Keep saying the grid
is a probe.

Grill cites (`origin/main` @ `5b7a934`; re-cite if they drift):

- Header “others F” (`oracle/driver.ml:3801–3804`)
- Areal miss → `-1` → `'F'` (`:4354–4368`)
- Open cells = 80×80 grid (`:4332–4358`; header `:3778`)
- EE hardcoded 2 (`:4359`; `RelateCurveMatrix.v : geom_de9im_ee_nonempty`)

## Acceptance

1. A circular / chord (`C` / `A`) pair that the analytical kernels
   report empty still prints `F` in those **computed** cells. Same
   kernels as `ARC_ARC_XY` / `ARC_SEGMENT_XY` / `HOLES_DISJOINT`
   (`docs/curve-relate-matrix-lemma-reuse-map.md`).
2. A lineal cell the header already calls undistinguishable prints
   `?`, not `F`.
3. An areal open-cell miss after an exhausted 80×80 probe prints
   `?`, not `F`. A hit still sets the open cell to `2`.
4. EE stays `2` (`RelateCurveMatrix.v : geom_de9im_ee_nonempty` /
   `two_geometries_exterior_meet`). Do not rewrite EE to `?`.
5. Mode header still says the open cells are probed by a grid, and
   states that an exhausted probe leaves `?`: no sample found. That
   is not `RelateCurveMatrix.v : cell_none_iff_empty`.
6. Tolerances `1e-12` / `1e-9` stay interface-boundary float. Do
   not retune them.
7. `docs/verified-claims.md` `RelateCurveMatrix.v` row records the
   alphabet (not only the dimension deferral).

Grid completeness (“miss ⇒ empty”) is a **research park**
(ADR-0002). Not required to emit an honest `?`.

E/B refuse is `523-a` / #603, not this ticket. If #603 has not landed,
do not use an E/B pair as the alphabet witness.

## After this ticket

Ticket 11 precondition 3 can be marked met **only if** the owner
treats the landed slices as resolving ticket 523. The implement
letter does not auto-retire that issue.

## Non-goals

Shared pins stay put. Decline golden stays `UNSUPPORTED`. Do not
implement leftover `Ⅰ` / `Ⅱ`. Do not mint `Ⅲ`. Do not remint
ADR-0004. Do not add a CONTEXT name for per-cell unknown unless
`/domain-modeling` + owner accept. Do not comment on GitHub issue
523 unless the user says `comment`.

## Resolution

**Closed 2026-08-30.** Lineal undistinguished cells and areal `-1`
probe misses print `?`. C/A kernels that reported no contact keep `F`.
EE stays `2`. Mode header names the probe and the exhausted-probe `?`.
Witness `523-c-driver-unknown`. Ticket 523 stays open.
