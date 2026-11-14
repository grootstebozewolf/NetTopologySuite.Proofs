<!-- doc-kind: guide -->
# ADR-0003 — Interior is two-tier: OGC open interior specifies, ray parity computes

| Field | Value |
|---|---|
| **Order** | ADR-0003 |
| **Status** | **Accepted** — 2026-08-22 |
| **Deciders** | Jeroen Bloemscheer (BDFL) |
| **Superseded by** | — |

---

## Context

The corpus has two different notions of "inside a ring" and has never said which
one is the specification. The ambiguity is not academic — it is the single
blocker on the nine-cell DE-9IM capstone and the reason six warnings in the
GEOS differential rung have sat undecided since August.

**The two notions.** `theories/Overlay.v:150 edge_crosses_ray` uses strict
inequalities, and `point_in_ring` (`:183`) is the parity of those crossings. The
resulting region is **half-open**, and one theorem makes that concrete:

```coq
(* theories/RectangleJCT.v:182 *)
point_in_ring_rect_iff :
  point_in_ring p (rect_ring x0 y0 x1 y1) <-> (y0 < py p < y1 /\ x0 <= px p < x1)
```

The left edge counts as interior; right, top and bottom do not. Meanwhile
`RelateCurveMatrix.v:181` sets `in_stratum SInt g p := point_set g p` (parity)
while `SBnd := geom_boundary` is closed `between` on any edge — so **SInt and
SBnd overlap**, which no OGC matrix admits.

**What the ambiguity costs.** The same half-openness that makes the rect II cell
free (`RelateNGRect.v:305` — A gives `px p < ax1`, B gives `ax1 <= px p`) makes
the BI and side-E\* cells *nonempty* against a matrix specifying `F`. That
mismatch is the nine-cell capstone leftover recorded on
[`docs/relate-ng-status.md`](../relate-ng-status.md) (still open) and tracked
for a second pass at #67 in
[`docs/scout/tickets/closed/11-retire-67-second-pass.md`](../scout/tickets/closed/11-retire-67-second-pass.md) (overtaken 2026-09-01).

The same convention appears on the oracle side — `POINT_IN_CURVE_RING`'s header
says boundary cases are excluded by strict inequalities *"as in
`Overlay.edge_crosses_ray`"* — and it is what four of the six WARNs in
`docs/geos-oracle-rung-2026-08.md` disagree about: points on the chord `y=0` are
oracle `IN` (parity region) but GEOS `contains=false` (boundary).

## Decision

**Interior is two-tier, and the tiers have distinct jobs.**

| Tier | Meaning | Where |
|---|---|---|
| **Specification** | the OGC **open** interior — `0 < gtri` for triangles, strict box for rectangles | what DE-9IM matrices and predicates are stated against |
| **Computation** | half-open **ray parity** — `point_in_ring` via `edge_crosses_ray` | what the algorithms and the oracle actually evaluate |
| **Bridge** | `gtri_point_in_ring_imp_pos` (`theories/RelateNGTouchCells.v:115`, Qed) and siblings | the only sanctioned route from computation to specification |

**`ring_complement` and `ray_avoids_vertices` are permanent, load-bearing
guards — not deferrals.** They are the bridge's hypotheses, and they are
*maximal*: `theories/RelateNGTouchRED.v:170
touch_triangle_ii_separation_not_unconditional` is **Qed** and exhibits two CCW
triangles sharing the edge `(0,0)–(0,2)` with `p = (−1,1)` in both interiors, so
the guard-free statement is false. The bridge header says so directly: *"The
unguarded statement is FALSE"*.

This is what the code already does. The ADR declares it, so it stops reading as
an unfinished migration.

## Consequences

- **The nine-cell capstone becomes tractable.** BI and side-E\* are specified
  against the open interior, so a matrix asserting `F` is provable; parity
  results reach it through the bridge, carrying the guards. The blocker was the
  undeclared conflation, not missing geometry.
- **Four GEOS WARNs are reclassified from undecided to expected.** Chord `y=0`
  points are outside the *specified* interior and inside the *computed* parity
  region; GEOS reports the specification, the oracle reports the computation, and
  both are right about their own tier. `docs/geos-oracle-rung-2026-08.md` should
  say that rather than leaving them open.
- **The apex WARN is a different convention and stays.** Tangent and
  vertex-grazing rays are the `ray_avoids_vertices` genericity guard. No decision
  removes it inside the parity model; only leaving parity would, and the
  specification tier is precisely where that already happens. Two conventions,
  one migration.
- **A new obligation on anything parity-shaped**: a theorem stated over
  `point_in_ring` does **not** state an OGC fact until it crosses the bridge.
  Claims should say which tier they are in. This is a documentation rule with
  teeth — `in_stratum SInt := point_set` currently reads as a specification and
  is a computation.
- **What this does not do**: it does not re-base `point_set` on `0 < gtri`
  (rejected as the same endpoint at far higher cost), and it does not bless
  half-open parity as the OGC interior (rejected: that permanently blocks the
  capstone and freezes the WARNs).
