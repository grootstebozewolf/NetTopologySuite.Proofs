<!-- doc-kind: guide -->
# ADR-0004 — Zoo length via a thin ExactCurve interface; cubic Bézier replaces quadratic in the Bible

| Field         | Value                                                        |
|---------------|--------------------------------------------------------------|
| **Order**     | ADR-0004                                                     |
| **Status**    | **Accepted** — decided by Joost (BDFL), 2026-08-27 (#508 grilling session) |
| **Deciders**  | Joost (BDFL)                                                 |
| **Date**      | 2026-08-27                                                   |
| **Superseded by** | — (none)                                                 |

---

## Context (self-contained)

Issue #508 opens the Bible §4.2 `length()` obligation across the Zoo (see
CONTEXT.md, *Exact curves*, for both terms). Two structural questions block
every implementation attempt:

1. **Carrier.** `theories/CurveGeometry.v` defines
   `CurveSegment := CSChord | CSArc`, consumed by 66 theory files carrying
   every validity, simplicity, offset, buffer and DE-9IM result. Elliptic,
   Bézier, clothoid and NURBS segments are structurally *inexpressible* in a
   `CurveRing`, so zoo length has no type to be stated over.

2. **Bézier degree.** Bible §4.1 lists `ExactQuadraticBezier` (chosen for its
   closed-form parabolic-arc length, §5 Year-2 opener). But nothing in the
   wild ships a quadratic-only Bézier segment: Esri's `BezierCurveSegment`
   is cubic, the corpus's `RelateBezier3.v` is cubic, the oracle's `B` token
   is cubic (8 coordinates), and ISO/IEC 13249-3:2016 has no Bézier at all.
   The zoo membership criterion fixed in the #508 grilling — *curves living
   in the wild engines, never curves that are easy to prove* — contradicts
   the Bible's roster.

## Decision 1 — thin interface, not an inductive extension

Zoo length obligations are stated against a thin Coq `ExactCurve` interface
(a record of obligations per type: carrier, start, end, metric length against
the canonical `curve_length` spec, plus the chord/control-polygon sandwich
where meaningful) — the **length slice** of the Bible §4.2 protocol. `pointAt`
and `toLinear` obligations are deliberately excluded: each drags in its own
epic (parameterization choices; the whole densify contract), and Bible §2.4/§6
forbid growing the common surface ahead of need.

Extending the `CurveSegment` inductive (adding `CSBezier3`, `CSElliptic`, …)
is **deferred to its own future ADR**. It is a 66-file campaign whose payoff —
zoo members inside `CurvePolygon` validity/DE-9IM — is not what §4.2 asks for.

*Rejected alternatives:* extend the inductive now (blast radius without §4.2
payoff); a parallel zoo segment type with an embedding (creates the
parallel-universe hazard the CurveCollection retirement documents).

## Decision 2 — Bible §9 amendment: `ExactCubicBezier` replaces `ExactQuadraticBezier`

Under Bible §9 change control (sign-off: the BDFL, who made this decision),
the zoo's Bézier member becomes **cubic**. Rationale: the wild-provenance
membership criterion rules; every existing corpus and oracle artifact is
already cubic; degree elevation quadratic→cubic is exact and rational, so no
quadratic fact is lost. **Acknowledged cost:** cubic arc length has no
elementary closed form, so §5's Year-2 order loses its premise and is
re-derived as **Ellipse → Cubic Bézier → Clothoid → single-span NURBS**, with
the 3-point-arc ↔ `rx = ry` elliptical bridge theorem as the ellipse's first
rung (the last closed-form equality target in the zoo, sanctioned by §4.3's
affine-reduction rule).

The fork edit (`doc/EXACT_CURVE_BIBLE.md` on `feature/sfa-curve-rgr` in
`grootstebozewolf/jts`, §4.1 + §5 + amendment record) was signed off by merge
of the fork's PR #125 on 2026-08-27.

## Consequences

- Per-type instances of the interface land independently, in the re-derived
  order; the privileged CircularArc instance closes the M-LEN debt
  (rectifiability of `r·θ` against `curve_length`, plus additivity).
- Ellipse and clothoid tiers use the conditional-hypothesis idiom of
  **ADR-0001** (named Section hypotheses, externally witnessed Qed in
  `clothoid-halley-coq`), with in-corpus discharge registered as Technique
  park work; NURBS starts witness-scoped.
- Differential gating uses the Oracle-stable criterion (CONTEXT.md):
  golden-vector agreement `|Δ| < max(1e-9, 4·ulp(reference))`, ≥ 99 %
  iteration agreement where iterative. Oracle segment tokens are letter-style
  projections of the ISO/IEC 13249-3:2016 WKT grammars (`ELLIPTICALCURVE`,
  `CLOTHOID`, `NURBSCURVE`), cited by clause in the token doc comments.
