# CRV-TOUCH · What do exact and robust kernels do at a tangency?

topic: docs
topics: arc, overlay
claimId: CRV-TOUCH
witness: none
kind: research
lane: green

## Reconstruction honesty

This file is a **reconstruction** of the 2026-09-07 AFK research note
that lived only as local tip `af4ca0a` on branch
`research/crv-touch-tangency` (cut from `main` @ `67506cb`). That SHA
was never pushed and is gone from reachable machines. The Notion
ticket that closed the card still holds the Resolution, including
findings marked *verbatim from the note*.

This is **not** a bit-identical replay of the lost blob. Line count of
the original was recorded as ~545; this file restates those findings
as a readable note. No new algebra is derived. No DOI is invented.
Citations are those the ticket already names, plus in-repo pointers
the findings already name (`oracle/driver.ml`, ADR-0007).

Ticket (source of the Resolution):
<https://app.notion.com/p/3d41c9833b068175854bfbdd114ea92c>

## Question

When two circular arcs, or an arc and a line, are tangent, what do
existing exact and robust intersection kernels return, and how do they
decide tangency?

The decision ticket *How does the cook decide a kiss?* waits on these
facts. ADR-0007 (Accepted 2026-09-07) keeps three tangency decision
procedures live and does not pick one: exact rational discriminant,
identity by construction, ulp-floored window. This note surfaces what
the published kernels actually do. It does not pick among those three
procedures and it does not edit the ADR.

**Resolves when** a research note records, per source:

1. Does it return a tangent point as a node?
2. Is tangency decided exactly (rational / algebraic) or by a window?
3. Does it distinguish tangent from crossing in the result?

## Sources actually read (2026-09-07 AFK)

Primary only, as the card required. Provenance is branch-head / tag,
not per-file commit SHAs (see Gaps).

| Source | What was read | Arc–arc / arc–line constructor? |
|---|---|---|
| CGAL `Circular_kernel_2` and the algebraic kernel it rests on (`Algebraic_kernel_for_circles`) | master + v6.2.1 source and manual | **Yes** |
| locationtech/jts `CircularArcs` or successors; `CGAlgorithms` / `LineIntersector` at degenerate tangency | upstream `master` | **No** |
| GEOS circular-string intersection at tangency | `main` + tag `3.15.0` | **Yes** (`CircularArcIntersector`, ≥ 3.15.0) |
| Priest 1991 §7 (line–segment only) | full text, Shewchuk's mirror | **No** — straight objects only |
| Fortune & Van Wyk | 1996 TOG full text; 1993 SoCG abstract only | **No** — straight objects only |

Unreachable on that day (recorded, not silently skipped): Priest's
IEEE page and 1992 thesis; the 1993 SoCG full text.

## Findings at a glance

Of the five sources, exactly two contain an arc–arc / arc–line
intersection constructor: CGAL `Circular_kernel_2` (via
`Algebraic_kernel_for_circles`) and GEOS ≥ 3.15.0
`CircularArcIntersector`.

| Question | CGAL `Circular_kernel_2` | GEOS `CircularArcIntersector` | Upstream JTS | Priest §7 | Fortune & Van Wyk |
|---|---|---|---|---|---|
| Tangent point as a node? | Yes — one point | Yes — one point (coalesced) | No arc oracle | n/a (segments) | n/a (segments) |
| Decide tangency how? | Exact sign of a rational discriminant when `FT` is exact | `double` `==` / `!=` / `<` / `>` | — | exact-decide / round-once on a linear system | exact homogeneous integer (linear language) |
| Distinguish tangent from crossing? | Yes, via multiplicity `2` vs `1` | No — kiss and a proper single crossing look the same | — | no double root exists | cannot express an arc |
| Window / epsilon? | None in the `solve` routines | In-source TODO for tolerance; `PrecisionModel` does not widen the test | — | input precision, not a tangency window | none (exact integer) |

Both arc kernels return the tangent point as a **single** intersection.
A cook built on either would mint **one hen** at the kiss.

## 1. CGAL `Circular_kernel_2`

### 1.1 What it is

CGAL's circular kernel, resting on `Algebraic_kernel_for_circles`, is
the only exact arc–arc / arc–line intersection constructor among the
five sources. `Exact_circular_kernel_2` fixes `NT = Gmpq` (or
`Quotient<MP_Float>`).

The manual sentence the note recorded:

> The robustness of the package relies on the fact that the algebraic
> kernel provides exact computations on algebraic objects.

### 1.2 One kiss point, decided by discriminant sign

CGAL returns the tangent point as a single intersection by an explicit
`sign_disc == ZERO` branch. Tangency is decided **exactly** when the
kernel `FT` is exact: the discriminant is a rational expression in the
coefficients, signed with `CGAL::sign`. No epsilon appears in the
`solve` routines.

The tangency discriminant CGAL signs is

```text
2·d²·(r1² + r2²) − ((r1² − r2²)² + (d²)²)
```

That is the expression the lost note recorded. This reconstruction
does not rearrange it. See §6 for the recorded correspondence with
this repo's `discq`.

### 1.3 Multiplicity distinguishes tangent from crossing

Only CGAL distinguishes tangent from crossing, and only via
multiplicity. The output pair is

```text
std::pair<Circular_arc_point_2, unsigned>
```

The unsigned field is `2` for a double root and `1` for a transversal
one. The manual describes the field as "the multiplicity of the
corresponding intersection point" without saying that 2 means tangent.
That reading is in the source comment `// one double root`.

CGAL's 2D Arrangements traits
(`Arr_geometry_traits/Circle_segment_2.h`) re-implement the identical
test with `mult = 2` and the comment "A single tangency point".

### 1.4 The kiss point is rational

At a tangency CGAL's point coordinates are rational:
`Root_of_2(x_base)`, no radical. Transversal roots are
`base ± coeff·√disc` (`Sqrt_extension`).

So the kiss hen is the one arc–arc intersection whose identity is
decidable by `FT` equality **without** algebraic-number comparison.

### 1.5 What a cook would see

A cook built on this kernel would mint one hen at the kiss. The
multiplicity field is available if the cook wants to *label* that hen
as tangent rather than transversal; the point itself is a single node
either way.

CGAL with `double` `FT`, and the `CGAL_CK_EXPLOIT_IDENTITY`
shared-endpoint branch, were **inferred** from source, not run. See
Gaps.

## 2. GEOS ≥ 3.15.0 `CircularArcIntersector`

### 2.1 What it is

GEOS 3.15 is the other published arc–arc / arc–line constructor.
`CircularArcIntersector` is the kernel. There is no JTS upstream
equivalent (see §3).

### 2.2 One kiss point, by coalescence

GEOS also returns the tangent point as a single intersection, but not
by an explicit tangency branch. It does it by coalescence:

- `h = sqrt(r1² − a²)` is 0 at a kiss,
- the two candidate roots are equal,
- `isect1 != isect0` drops the second.

A cook built on this kernel would still mint one hen at the kiss. The
mechanism is "the two roots happened to compare equal", not "we
classified a double root".

### 2.3 Decision is exact comparison of inexact doubles

GEOS decides tangency by exact comparison of inexact `double`s. The
tests the note recorded:

```text
d  > r1 + r2
d  < |r1 − r2|
dd < 0
d  == 0
p1.x == x0 + r
```

The circle centre is computed in `double`. The source carries:

```text
// TODO because the circle center calculation is inexact we need some
// kind of tolerance here.
```

The optional `PrecisionModel` rounds the **output** point after the
decision. It does not widen the test. So the TODO is live: near-miss
pairs can take the disjoint / crossing / coincident branches according
to how the doubles landed, and snapping the reported point afterwards
does not change that classification.

### 2.4 No tangent-vs-crossing distinction

GEOS's `intersection_type` has no tangent value and no `isProper()`.
A kiss and a proper single crossing are indistinguishable in its
result. The only observable is "one intersection point".

### 2.5 Overlay path (3.15.0)

GEOS 3.15.0 puts this arc kernel on the overlay path:

- `Geometry::intersection` of two `CircularString`s no longer throws.
- `EdgeNodingBuilder` uses a `SimpleNoder` with `ArcIntersectionAdder`
  when `inputHasCurves`.
- Noding validation is skipped for curved input:
  `if (doValidation && !inputHasCurves)`, with
  `// TODO: Support arcs in ValidatingNoder`.
- The snapping fallbacks throw for curves.
- RelateNG, `IsValidOp` and `IsSimpleOp` still throw on curved input.

So overlay of two circular strings can run and can node a kiss as one
point, while relate / valid / simple still fail closed, and the noder
that would *check* the noding is the one that is skipped.

Near-tangency behaviour was inferred from this code, not run. A
`GeosOracleBugHunt` pass against the oracle's `EXT_TANGENT` family
would settle it. See Gaps.

## 3. Upstream locationtech/jts

Upstream JTS `master` has **no** circular-arc intersection constructor.

- Issue #443 was closed to "FUTURE" in 2019.
- Epic #1195 (open) marks N-AA / N-AL "Still red".

`CircularArcs` and successors were the names the card asked to look
for. They do not supply an arc–arc or arc–line oracle on `master`.
`CGAlgorithms` / `LineIntersector` treat straight objects; their
degenerate-touch behaviour is the segment analogue in §7, not an arc
precedent.

There is therefore no JTS upstream arc oracle for a cook to copy, and
no JTS multiplicity or tangency flag to inherit. GEOS 3.15 is the
JTS-family engine that actually has the constructor.

## 4. Priest 1991 §7

Priest §7 is line–segment only. The full text was read from Shewchuk's
mirror. The paper never mentions tangency, double roots, or arcs.

Version 2 of the method behaves as follows for (line, segment):

- `u = 0, v ≠ 0` returns the endpoint **exactly**;
- `u = v = 0` returns "Intersection not unique".

That is the touch analogue for a linear system: copy the known
endpoint when the parameter says the meeting is there; refuse a unique
point when the system is degenerate.

The exact-decide / round-once shape has **no double root to extend**,
because the segment–line system is linear. Priest is not a precedent
for arc tangency. It is a precedent for the ADR-0007 shape "exact
sign, then a representable point".

Priest's IEEE page and 1992 thesis were unreachable on the research
day.

## 5. Fortune & Van Wyk 1996 TOG

Fortune & Van Wyk treat straight objects only and never mention
tangency, double roots, or arcs. The 1996 TOG full text was read; the
1993 SoCG full text was unreachable (abstract only).

Their LN cannot express an arc intersection at all. The language is
integer polynomials over `{+, −, ×}`. Rationals appear only via
homogeneous coordinates. Algebraic numbers are delegated to Yap /
LEDA `real`.

So "exact homogeneous integer output at a tangency" is a question the
language cannot pose for arcs. The paper is not a precedent for arc
tangency. It is, with Priest, a precedent for the ADR-0007 shape
"exact sign, then a representable point".

This reconstruction does not add a DOI. ADR-0007 already records the
venue identifiers for these two papers in its own References; this
note does not rest on those identifiers and does not extend them.

## 6. `discq` ↔ CGAL discriminant

The repo's `oracle/driver.ml` already classifies
`EXT_TANGENT` / `INT_TANGENT` with `NODES 1` by testing a four-factor
discriminant for zero in exact ℚ. The lost note recorded that CGAL's
signed discriminant is, **up to a constant factor**, the same form.

Recorded CGAL expression (from the Resolution; not rearranged here):

```text
2·d²·(r1² + r2²) − ((r1² − r2²)² + (d²)²)
```

In-repo `discq` as `oracle/driver.ml` already writes it (exact ℚ,
`DISC_OVERLAY`):

```text
diff  = d² + r1² − r2²
discq = 4·d²·r1² − diff²
```

Classification already in the driver, not new algebra:

- `discq > 0` → `CROSSING`, two nodes
- `discq = 0` → `EXT_TANGENT` or `INT_TANGENT` according to
  `d² ≶ r1² + r2²`, one node
- `discq < 0` → `DISJOINT` or `NESTED`

CGAL's arrangements traits (`Circle_segment_2.h`) re-implement the
identical test with `mult = 2` ("A single tangency point").

The correspondence is a recorded finding of the AFK note. This file
does not prove the constant-factor identity and does not add a third
formula.

## 7. Segment kernels at a touch

The segment kernels agree on the **touch analogue** (endpoint meeting,
not arc tangency).

JTS and GEOS `LineIntersector`:

- decide an endpoint touch by exact sign
  (`Orientation.index` → filter → DD, zero included) and `equals2D`;
- **copy** the endpoint rather than compute it — the recorded comment
  is *"Copying the point rather than computing it ensures the point
  has the exact value"*;
- mark it `isProper() == false`;
- still node it: `IntersectionAdder` adds every non-trivial
  intersection regardless of `isProper`.

Priest §7 version 2, as above: `u = 0, v ≠ 0` returns the endpoint
exactly; `u = v = 0` returns "Intersection not unique".

So the straight-object precedent for a kiss is: decide by an exact
sign (or an exact parameter), emit a point that is already in the
input, mark it improper if the API has that bit, and still insert it
as a node. That is identity-by-construction for a shared endpoint,
which ADR-0007 already treats as **not** a kiss. Two eggs sharing an
endpoint is the cook's existing case. A discriminant-zero tangency
is the case this card owns.

## 8. What this surfaces for the cook

ADR-0007 vocabulary (sheet / hen / egg / cook / `𝓘`) is assumed, not
reopened. Facts the kiss-decision ticket can use, without picking a
procedure:

1. **Count.** Both published arc kernels return one point at a kiss.
   A cook that follows either mints one hen, not two coincident hens
   and not zero.
2. **Exact vs window.** CGAL (exact `FT`) is the existence proof that
   an exact rational/algebraic decision is implementable and that the
   kiss coordinates are then rational. GEOS is the existence proof
   that a production overlay path currently decides by `double` `==`
   and already knows that is incomplete (the tolerance TODO).
3. **Label.** Only CGAL can tell the cook "this hen is a double root".
   GEOS cannot. If the cook needs a kiss certificate distinct from a
   transversal node, CGAL's multiplicity is the published precedent;
   GEOS's result type is not.
4. **Identity without radicals.** CGAL's kiss point is in `FT`;
   transversal points are `Sqrt_extension`. The kiss is the cheap
   identity case. That matches the oracle's `NODES 1` at
   `discq = 0`.
5. **No JTS oracle to port.** The JTS-family arc constructor is GEOS
   3.15, not locationtech/jts.
6. **Priest / Fortune** justify "exact sign, then a representable
   point" for the linear cook. They do not extend to a circle and
   they do not discuss a double root.
7. **Segment touch** justifies copying a known point when the meeting
   is an endpoint. It does not justify treating a tangency as a
   shared endpoint.

None of this invents a cook-mode keyword. ADR-0007 left an ADR-0006
kiss-hen keyword as a later CRV-TOUCH ticket after a prototype.

## 9. Gaps recorded

These were gaps in the original AFK note. They remain gaps. This
reconstruction does not close them.

- **GEOS near-tangency was inferred from code, not run.** A
  `GeosOracleBugHunt` pass against the oracle's `EXT_TANGENT` family
  would settle whether the `double` `==` path actually reports one
  node on the oracle's kiss fixtures, or slips into disjoint /
  crossing / coincident.
- **CGAL with `double` `FT`** was inferred, not run.
- **`CGAL_CK_EXPLOIT_IDENTITY`** (shared-endpoint branch) was
  inferred, not run.
- **Per-file commit SHAs were not recorded.** Provenance is
  branch-head / tag (CGAL master + v6.2.1; JTS master; GEOS main +
  3.15.0).
- **Priest's IEEE page and 1992 thesis**, and the **1993 SoCG full
  text**, were unreachable.

## 10. SUMMARY

SUMMARY ok — reconstruction of the 2026-09-07 CRV-TOUCH AFK note from
the Notion Resolution; not a bit-identical replay of lost tip
`af4ca0a`.

- Exactly two arc oracles exist among the five sources: CGAL
  `Circular_kernel_2` and GEOS 3.15 `CircularArcIntersector`.
- Both return **one kiss point**.
- CGAL decides by exact discriminant sign and reports multiplicity 2;
  the kiss coordinates are rational.
- GEOS decides by `double` `==` and drops the duplicate root; a TODO
  asks for tolerance; `PrecisionModel` does not widen the test; kiss
  and a single proper crossing are indistinguishable.
- Upstream JTS has no arc oracle (issue #443 FUTURE, 2019; epic #1195
  N-AA / N-AL still red).
- Priest §7 and Fortune & Van Wyk are segment-only; no tangency, no
  double root, no arcs. Both still support ADR-0007's "exact sign,
  then a representable point".
- CGAL's discriminant and the oracle's `discq` are the same
  four-factor form up to a constant; `discq = 0` is already
  `EXT_TANGENT` / `INT_TANGENT` with `NODES 1`.
- Segment kernels copy the endpoint on a touch and still node it.
- Gaps above stay open. No `theories/` change. No new algebra.
