<!-- doc-kind: finding
date: 2026-11-19
Provenance: 14cd7a4
Theorems: `CurvedKissObligation.v : t_ext_kiss`, `CurvedKissObligation.v : t_int_is_covers_not_kiss`, `RelateTouchDiscs.v : td_ii_empty`, `RelateTouchDiscs.v : td_bb_singleton`, `CircularCookSplit.v : leftover_shared_endpoint_not_touch`
-->
# Spec — CRV-TOUCH kiss (tangency hen, certificate, identity)

The destination of the CRV-TOUCH wayfinder map. Written 2026-11-19
from the Architect grill (seven decisions, Q1–Q7) and the throwaway
prototype `docs/scout/proto/CrvTouchKissStub.v` (14cd7a4). It assumes
ADR-0007's vocabulary (sheet, hen, egg, cook, `𝓘`, Empty ≠ Decline,
view) and does **not** edit ADR-0007. Per that ADR, a ticket may only
*propose* an amendment; the one this spec proposes is in
[Proposed amendment](#proposed-amendment-to-adr-0007).

topics: arc, overlay
claimId: CRV-TOUCH
witness: kiss-discs, arc-line-tangent

Board: [CRV-TOUCH · wayfinder map](https://app.notion.com/p/3d41c9833b068143b870c30feba956c3)
· parent card [Touch for noding](https://app.notion.com/p/3be1c9833b0681f8a944ce851d463236).

It is **not** a noder, **not** a fifth overlay op, **not** an
`OverlayNGCurve.TOUCH`, **not** an ADR-0006 cook-mode keyword, and does
**not** close JTS-side work (Option C `CurveSegmentNoder` stays on the
Bar 2 stack, off #7).

## Vocabulary (Q7)

- **Tangency**: two eggs whose supporting curves meet at a double
  root: circle–circle with `discq = 0`, or circle–line with `h² = 0`.
- **Kiss**: a tangency with σ = Ext. It matches `CurvedKissObligation.v`
  (closures meet, interiors disjoint) and DE-9IM TOUCH.
- **Pinch**: a tangency with σ = Int. It is the covers row, not TOUCH
  (`t_int_is_covers_not_kiss`).
- **Shared endpoint** is neither. Two eggs that both *end* at a point
  are Hit incidence (`leftover_shared_endpoint_not_touch`), handled by
  the existing cook.

## Decision procedure (Q1, Q2)

`𝓘` decides a tangency **exactly in ℚ** on the rational data of the
**uncooked input eggs**:

- circle–circle: (d² − r₁² − r₂²)² = 4·r₁²·r₂², i.e. `discq = 0`, with
  centres and r² rational (circumcentre of three rational points);
- circle–line: h² = r² − |o − F|² = 0, with F the rational foot.

The tangency point is rational:
c₁ + ((d² + r₁² − r₂²)/(2d²))·(c₂ − c₁) for two circles, and F for a
line. Span membership on each input egg is decided on rational data:
the chord parameter t ∈ [0, 1], and for an arc a₀→a₁→a₂ the point is
an endpoint or lies strictly on a₁'s side of chord a₀a₂.

**Decline** (named QEX) when any input is cooked or derived. That
covers an arc whose endpoint is a √ transversal hen, and overlapping
co-circular arcs. ℚ(√d) is not in the statement.

**Coincident circles Decline first.** If d² = 0 and r₁² = r₂², the
supporting circles coincide. 𝓘 returns Decline before it evaluates the
tangency-point formula, which divides by d². The `discq = 0` test alone
accepts this case, and ℚ's x/0 = 0 would then emit the common centre as
a Touch point. For two arcs on a coincident circle this is the
co-circular rule; for full circles or discs it applies all the same.
Concentric circles with r₁² ≠ r₂² have no contact and give Empty.
A zero-length segment (dx = dy = 0) is not a line and also Declines.

Ruled out:
- *identity by construction*: it never finds a tangency between
  independently drawn eggs;
- *ulp window* (JTS #38 `onString`, GEOS `double ==`): it mints hens
  that do not exist and cannot tell a kiss from a crossing.

## Certificate (Q4)

A tangency hen carries

> σ = Ext ⇔ d² − r₁² − r₂² > 0  σ = Int ⇔ d² − r₁² − r₂² < 0

which is a rational sign. An arc–line tangency is always Ext.
"Interiors are disjoint near the hen" is a **lemma from σ = Ext**
(`td_ii_empty`, `td_bb_singleton`), not the certificate. The
local-order (rotation-system) form is parked until the cook has a
rotation system.

Consumers read σ without recomputing geometry:

| Consumer | σ = Ext (kiss) | σ = Int (pinch) |
|---|---|---|
| DE-9IM | TOUCH; BB = 0, II = F (T-ext `FF2F01212`; arc–line `FF20F1102`) | covers row, II = 2 |
| V1 | CUP self-touch | SUB pinch on the shared boundary (`int_kiss_pinch`) |

## Binary64 (Q5)

Binary64 is a **sheet for the decision** and a **view for the
output**. Inputs are rationals, so the decision above is exact, with
no window and no precision Decline. Only the emitted tangency point is
rounded, once. The hen's identity is the rational point.

The oracle already obeys this: since T4b `0ddd021`,
`seg_circle_exact` and `circ_circ_exact` choose the 1-vs-2 count with
an exact `qeq h2q q0`, and `Q.to_float` touches only emitted
coordinates. The JTS fork's 45° bulge test (t = 5·√2 as a double,
asserting the tangent matrix) violates the rule. It is open in the fork,
not here.

## Identity (Q6)

A tangency hen **reuses** an existing hen (`ShareOne`) iff their
points are equal in ℚ. Otherwise it is minted. A tangency never mints
a second hen at an occupied point. Input-egg hens are rational. A
transversal hen `base ± coeff·√D` equals a rational point only if its
√ term is zero (a structural test). Control points are egg data and
never hens, even when the WKT spells the coordinate.

## Outcome shape (Q3) — ADR-0007 unchanged

| Case | Outcome |
|---|---|
| tangency, point in both input spans | **Touch**: one hen, σ attached; a kiss iff σ = Ext |
| tangency outside a span, or the curves miss | **Empty** |
| curves cross ((d² − r₁² − r₂²)² < 4·r₁²·r₂², or h² > 0) | **Hit** (`IZTouch_neq_IZHit`, `ICircGTouch_neq_ICircGHit`) |
| cooked / derived / irrational input, co-circular overlap, coincident circles (d² = 0, r₁² = r₂²), zero-length segment | **Decline** (named QEX) |

## Acceptance clause

The spec is met by a product module (sibling of
`RelateTouchDiscs.v`, name chosen at implement time) that states the
decision over ℝ² for rational input eggs and discharges these
witnesses. The prototype already passes them by `vm_compute`:

| # | Input | Required outcome |
|---|---|---|
| A1 | discs (0,0) r 1 · (2,0) r 1 (`ext_A`/`ext_B`) | Touch (1,0), σ = Ext, kiss; agrees with `t_ext_kiss` |
| A2 | discs (0,0) r 2 · (1,0) r 1 (`int_A`/`int_B`) | Touch (2,0), σ = Int, not a kiss; agrees with `t_int_is_covers_not_kiss` |
| A3 | `CIRCULARSTRING (-5 0, 0 5, 5 0, 0 -5, -5 0)` arc 1 · chord (−10,5)→(10,5) | Touch (0,5), σ = Ext, **minted** (control point) |
| A4 | same arc 1 · chord (5,−10)→(5,10) | Touch (5,0), σ = Ext, **reuses** the join hen |
| A5 | arc 2 · the same chord as A4 | the **same** join hen as A4 |
| A6 | arc 1 · chord (−10,−5)→(10,−5) | Empty (tangency off span) |
| A7 | discs (0,0) r 1 · (1,0) r 1 | Hit |
| A8 | any cooked input | Decline |
| A9 | discs (0,0) r 1 · (0,0) r 1 (coincident) | Decline, checked before the tangency point is computed; never Touch |

Additionally, and beyond the prototype:
- **ℝ bridge**: a σ = Ext tangency of two discs implies `disks_touch`,
  and σ = Int implies `disk_covers`.
- **Span-checked Hit**: a secant meeting neither span is Empty, not Hit.
  The prototype skips this.
- **Co-circular overlap** is detected and Declines. The prototype
  skips this.
- **Coincident circles** (A9) Decline before any division by d². The
  prototype gets this wrong: it returns `Touch (0,0) Int` for two equal
  discs, because `cc_point` divides by d² = 0.

Out of scope for acceptance: the ADR-0006 cook-mode keyword for a
tangency hen (a later ticket, now unblocked by the prototype), arc cook
termination (Curve noding / OV-NODING sisters), and the JTS noder kiss
(it keeps the parent card red).

## Proposed amendment to ADR-0007

This is for the BDFL to accept or reject; this spec does not edit the
ADR. Replace the first bullet of *CRV-TOUCH / RGR (vocabulary law, not
kiss)* (currently: "**Kiss** is external / internal circle tangency
and arc–line tangency (discriminant zero) …") with:

> - **Tangency** is circle–circle or circle–line contact at a double
>   root (discriminant zero). It mints one hen carrying σ ∈ {Ext, Int}.
>   A **kiss** is a tangency with σ = Ext (TOUCH). A tangency with
>   σ = Int is a **pinch** (covers). Two eggs sharing an endpoint is
>   neither; the cook already handles that case.

and replace "Three tangency decision procedures stay live …" with a
pointer to this spec (exact-Q on uncooked input eggs, Decline
otherwise).

OUTCOME: spec written. The map's grilling (Q1–Q7) and prototype are
green. Implementation and the ADR-0007 amendment are separate tickets.
