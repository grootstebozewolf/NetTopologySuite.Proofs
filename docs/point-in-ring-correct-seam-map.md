# `point_in_ring_correct` — seam map

**Status.**  Documentation only.  No Coq changes.  Maps every seam between
the corpus's `point_in_ring` (theories/Overlay.v:183) and the
correctness statement `point_in_ring_correct` that `OverlayCorrectness.v`
carries as an opaque `Variable` hypothesis (H1).  The output is a precise
gap inventory: what exists, what's missing, what each missing piece costs.

This is the artifact that makes a future JCT proof session *planned*
rather than exploratory.

Companion documents:

  - `docs/audit-phase3-milestone5.md` §4.2 — original JCT scout (S8).
  - `docs/ecosystem-search-2026-05-29.md` — ecosystem audit (fourcolor,
    GeoCoq, mathcomp-analysis).
  - `theories-flocq/OverlayCorrectness.v` — the H1 hypothesis is stated
    here as a Section Variable.

---

## §1 — The target statement

```coq
Theorem point_in_ring_correct :
  forall (p : Point) (r : Ring),
    ring_closed r ->
    ring_simple r ->
    ring_has_minimum_points r ->
    point_in_ring p r <-> geometric_interior p r.
```

Where `geometric_interior p r` is: `p` lies in the bounded connected
component of `R² \ image(r)` — the standard Jordan-curve-theorem notion
of the topological interior of a simple closed polygon.

**Note on shapes.**  `point_in_ring : Point -> Ring -> Prop` (theories/
Overlay.v:183) returns a `Prop`, defined via the mutually inductive
`ray_parity_odd` / `ray_parity_even` (Overlay.v:161-179) on the edge
list.  Hence `point_in_ring_correct` is a biconditional (`<->`), not a
`reflect`-style bool↔Prop lemma — the correctness statement does not
need a separate `Bool.reflect` layer.

**Note on `geometric_interior`.**  The predicate does NOT exist in the
corpus.  `OverlayCorrectness.v:71` opens it as a Section-bound
`Variable geometric_interior : Point -> Ring -> Prop`.  On Section
close, every theorem in the file becomes `forall geometric_interior,
...`.  Consumers instantiate from whatever JCT toolkit they have on
hand.  No Axiom / Parameter / Admitted is pulled.

**Note on the H1 wording in `OverlayCorrectness.v`.**  The current
`OverlayCorrectness.v` H1 (lines 96-98) drops `ring_has_minimum_points`
and reads:

```coq
(forall (q : Point) (r : Ring),
   ring_closed r -> ring_simple r ->
   point_in_ring q r <-> geometric_interior q r) ->
```

The proper formulation of `point_in_ring_correct` would re-add the
`ring_has_minimum_points` precondition (a triangle or larger).  H1 is
strictly stronger than the target by omitting the minimum-points
guard; tightening H1 to match `point_in_ring_correct` is part of
the upgrade path (§5 Step 4).

---

## §2 — The seven seams

For each seam: name, what exists, what's missing, cost estimate, which
installed library (if any) helps.

### Seam 1 — Algorithm → specification

`point_in_ring p r` computes the crossing-number parity of a horizontal
rightward ray.  The specification says this parity has the *right
value* iff `p` is in the geometric interior:

```
point_in_ring p r ≡ ray_parity_odd p (ring_edges r)
            ↕  (?)
crossing-number(ray-from-p, r) is odd
            ↕  (?)
p ∈ bounded component of R² \ |r|
```

  - **Exists**: `point_in_ring` (Overlay.v:183) and `ring_edges`
    (Overlay.v:110).
  - **Missing**: `geometric_interior` (the specification) plus the
    connection from crossing-number parity to geometric-interior
    membership.
  - **Cost**: defining `geometric_interior` over fourcolor's
    `realplane.region` is ~1 session (the H1 internalisation
    side-deliverable from `docs/ecosystem-search-2026-05-29.md` §6).
    The *connection* is JCT, thesis-scale.
  - **Library**: fourcolor `realplane.v` supplies the topology
    vocabulary (`region`, `open`, `closure`, `connected`); does NOT
    supply the bridge from Stdlib R to fourcolor's `Real.structure`
    (separate seam, see Seam 6).

### Seam 2 — Crossing number → winding number

For simple closed curves, the parity of the ray-crossing count equals
the winding number mod 2.  For simple polygons (which `ring_simple`
guarantees up to proper crossings; see Seam 4 for degeneracies), this
parity correctly identifies interior vs exterior.  Classical result;
proofs typically go through homotopy or piecewise-linear deformation.

  - **Exists**: `ring_simple` (Overlay.v:244-249) — "no two distinct
    edges intersect properly".
  - **Missing**: a formal statement connecting crossing parity to the
    winding number, or directly to interior/exterior membership, for
    simple polygons.
  - **Cost**: 2-4 sessions from scratch.
  - **Library**: NONE.  mathcomp-analysis has `solvable/jordanholder.v`
    (Jordan-Hölder for finite groups) and `analysis/charge.v`
    (Jordan-Hahn decomposition for signed measures) — both spurious
    name matches per `docs/ecosystem-search-2026-05-29.md` §4.  No
    winding-number library is installed.  The prompt's claim that
    mathcomp-analysis "has Seam 2" does NOT survive contact with the
    ecosystem audit; see §4 finding 2.

### Seam 3 — Ray–segment crossing count

`point_in_ring`'s correctness rests on `edge_crosses_ray` (Overlay.v:
149-155) correctly characterising which segments of the ring intersect
the rightward ray from `p`.  The current definition is:

```coq
Definition edge_crosses_ray (p : Point) (e : Edge) : Prop :=
  let (a, b) := e in
  (py a < py p < py b /\
     px p < px a + (px b - px a) * (py p - py a) / (py b - py a))
  \/
  (py b < py p < py a /\
     px p < px b + (px a - px b) * (py p - py b) / (py a - py b)).
```

A *correctness lemma* `edge_crosses_ray_correct` would state: this
predicate holds iff the open ray `{(px p + t, py p) : t > 0}` strictly
crosses the open segment from `a` to `b`.

  - **Exists**: `edge_crosses_ray` (the predicate), `cross_R_pt`
    (theories/ArcOrient.v:64) — the 2D orientation cross product.
  - **Missing**: a Qed-closed correctness lemma for `edge_crosses_ray`
    relative to a formal "ray crosses segment" predicate.  No
    `segment_crosses_ray` predicate exists in the corpus.
  - **Cost**: 1-2 sessions.  Purely linear algebra; no topology.  Note
    the prompt's optimistic finding ("cross_R_pt already handles the
    orientation argument") is partially true: `cross_R_pt p a b`
    encodes the half-plane sign, but the current `edge_crosses_ray`
    uses the *linear-interpolation x-formula* `px a + (px b - px a) *
    (py p - py a) / (py b - py a)`, NOT the cross-product sign.  The
    two are equivalent given the y-straddle, but reconciling them is
    ~½ session of algebra, not a freebie.  See §4 finding 1.
  - **Library**: NONE needed; corpus has everything required.

### Seam 4 — Degenerate ray cases

The current `edge_crosses_ray` uses **strict** inequalities everywhere
(`py a < py p < py b`).  This silently classifies the following as "not
crossing":

  - `p` exactly at a vertex of an edge (`py p = py a` or `py p = py b`).
  - `p` directly below or at a horizontal edge (`py a = py b`).
  - `p` on the interior of an edge (the second disjunct's `px p < ...`
    is false at equality).

This is the **standard "generic position" convention**: the algorithm
is correct *provided* `p` is not on the boundary and the ring has no
horizontal edges aligned with `py p`.  `ring_simple` does NOT
preclude either; degeneracy is unhandled.

  - **Exists**: nothing in the corpus that addresses ray degeneracies.
  - **Missing**: either
    (a) a precondition on `p` and `r` excluding degenerate alignments
        (`py p` distinct from every vertex's y, no horizontal edges at
        height `py p`), or
    (b) a stronger algorithm that handles degeneracy correctly
        (half-crossing convention at horizontal edges, perturbed-ray
        argument, or symbolic-perturbation tie-breaker).
  - **Cost**: 1-3 sessions depending on approach.  Approach (a) is
    cleanest as a precondition but reduces the theorem's domain;
    approach (b) is closer to the production algorithm but requires
    limit-style reasoning.
  - **Library**: NONE.

### Seam 5 — Simple polygon → Jordan curve

`ring_closed` + `ring_simple` + `ring_has_minimum_points` (≥ 4 points,
i.e., ≥ 3 distinct vertices plus the repeated closing vertex) gives a
simple closed polygon.  A simple closed polygon is a Jordan curve.
The Jordan curve theorem says it divides `R²` into exactly two
connected components — the bounded *interior* and the unbounded
*exterior*.

  - **Exists**: `ring_closed` (Overlay.v:235-236), `ring_simple`
    (Overlay.v:244-249), `ring_has_minimum_points` (Overlay.v:
    262-263).
  - **Missing**: JCT for simple polygons over Stdlib `R²`.
  - **Cost**: thesis-scale.  Confirmed RED from
    `docs/audit-phase3-milestone5.md` §4.2 and
    `docs/ecosystem-search-2026-05-29.md` §5.
  - **Library**: NONE direct.  fourcolor's `proof/jordan.v` proves
    `planar G -> Jordan G` for hypermaps — **combinatorial** Jordan
    (no Möbius paths), NOT geometric JCT for `R²` polygons.  GeoCoq
    has zero polygon-level results.  mathcomp-analysis has no JCT.

### Seam 6 — Connected components → interior / exterior

Given JCT delivers two connected components, the *bounded* one is the
interior.  Identifying which component is bounded requires either a
compactness argument or an explicit diameter bound, plus the connection
from fourcolor's abstract `Real.structure` to Stdlib `R`.

  - **Exists**: fourcolor's `realplane.v` (`open`, `closure`,
    `connected`, `region`, `border`, `simple_map`).
  - **Missing**:
    (a) a `Real.structure` instance for Stdlib `R` (fourcolor is
        parametric over an abstract real-numbers carrier; the bridge
        is not provided);
    (b) identification of the bounded component;
    (c) a translation from the corpus's `Ring : list Point` to a
        fourcolor `region` / `border`.
  - **Cost**: 3-5 sessions if the `Real.structure` bridge (item a)
    is built first; the bridge itself is 2-3 sessions per
    `docs/ecosystem-search-2026-05-29.md` §5.
  - **Library**: fourcolor `realplane.v` (with the bridge work).

### Seam 7 — Geometric interior → `point_in_ring` output

The composition: `p ∈ bounded component` iff `point_in_ring p r`.
Requires chaining seams 1-6 into a biconditional, observing the
preconditions (`ring_closed`, `ring_simple`,
`ring_has_minimum_points`) and discharging the degeneracy guard
from Seam 4.

  - **Exists**: nothing.
  - **Missing**: the full composition.
  - **Cost**: 1-2 sessions of proof engineering once seams 1-6 are
    closed.
  - **Library**: NONE additional.

---

## §3 — Seam dependency graph

```
Seam 3 (edge_crosses_ray_correct)   — independent, 1-2 sessions
        ▼
Seam 4 (degeneracy handling)         — depends on Seam 3, 1-3 sessions
        ▼
Seam 2 (crossing → winding)          — depends on Seams 3, 4, 2-4 sessions
        ▼
                                        ┐
Seam 6 (components → interior)       —  │ depends on Real.structure bridge
        ▼                               │ (2-3 sessions) + 1-2 sessions
                                        │ identification logic
Seam 5 (Jordan curve)                —  │ depends on Seam 6, thesis-scale
        ▼                               │
                                        ┘
Seam 1 (algorithm → spec)            — depends on Seams 2, 5
        ▼
Seam 7 (composition)                 — depends on all others, 1-2 sessions
```

Critical-path dependency: **Seam 5 (geometric JCT)** is the only
thesis-scale node.  Removing it (or making it tractable via a future
ecosystem addition) collapses the whole chain to ~10-15 sessions of
engineering work.

---

## §4 — What's tractable without JCT

Seams 3 and 4 are independent of JCT.  Closing them produces:

  - `edge_crosses_ray_correct` — a verified ray–segment intersection
    test.  States that the predicate fires iff the open ray from `p`
    strictly crosses the open segment.  Proof is ~80-150 lines of
    linear algebra over Stdlib `R`.

  - `point_in_ring_degenerate_safe` — a characterisation of the
    algorithm's behaviour on degenerate inputs, OR a precondition
    excluding them.  Cleanest formulation: a `generic_ray_position p r`
    predicate plus the lemma `generic_ray_position p r ->
    point_in_ring_well_defined p r` (where "well-defined" is the
    algorithm's parity matching the underlying geometric parity, by
    induction on the edge list).

These are real corpus deliverables independent of any JCT progress.
They strengthen the algorithm's documented properties and would be
load-bearing if JCT ever becomes tractable.

### Findings — adjustments to the prompt's expectations

**Finding 1 — Seam 3 is NOT cheaper than the prompt's "less than 1
session" estimate.**

The prompt claims `cross_R_pt` already handles Seam 3's orientation
argument.  The corpus's `edge_crosses_ray` (Overlay.v:149-155) does
NOT use `cross_R_pt`; it uses the linear-interpolation x-coordinate
formula `px a + (px b - px a) * (py p - py a) / (py b - py a)`.
Equivalence with the cross-product formulation requires a small
algebraic detour:

```
(px p < px a + (px b - px a) * (py p - py a) / (py b - py a))
  ⟺  given py a < py p < py b:
  ⟺  cross_R_pt p a b * sign(py b - py a) > 0
```

This is ~½ session of algebra, not zero.  Seam 3 remains tractable at
1-2 sessions; the "freebie" expectation does not survive the grep.

**Finding 2 — mathcomp-analysis does NOT have Seam 2.**

The prompt suggests mathcomp-analysis might have a crossing →
winding-number bridge already.  `docs/ecosystem-search-2026-05-29.md`
§4 confirms (RED) that mathcomp-analysis carries only:

  - `solvable/jordanholder.v` — Jordan-Hölder for finite groups
    (composition-series uniqueness).
  - `analysis/charge.v` — Jordan-Hahn decomposition for signed
    measures.

Both are name-collision false positives.  No winding-number theory, no
crossing-number theory, no geometric Jordan results.  Seam 2's cost
estimate (2-4 sessions from scratch) stands; **no upgrade**.

**Finding 3 — `edge_crosses_ray` handles degeneracies by *exclusion*,
not by a robust algorithm.**

The standard analysis (the prompt's perturbed-ray / half-crossing
convention) does NOT match what the corpus does.  The corpus's strict
inequalities silently classify:

  - vertex hits as not-crossing,
  - horizontal edges at height `py p` as not-crossing,
  - on-edge points as not-crossing.

This is the "generic position" convention and is internally
consistent, but means `point_in_ring_correct` MUST carry a
`generic_ray_position` precondition OR the theorem reads "for points
not on the boundary and rings with no edge at height `py p`".  This
affects the *statement* of `point_in_ring_correct`, not just its
proof.  See Seam 4 for the cost implications.

---

## §5 — The conditional upgrade path

If JCT becomes available (new library, future Coq ecosystem addition,
or in-corpus thesis investment), the path to upgrading
`overlay_ng_correct_conditional` from H1-conditional to unconditional
is:

```
Step 0: Internalise H1 in OverlayCorrectness.v             ~1 session
        Replace the opaque Variable with a concrete
        `geometric_interior` defined over fourcolor's
        `realplane.region`.  The conditional theorem
        becomes strictly stronger: gap stated in concrete
        topology rather than as a parameter.
        (Side-deliverable per ecosystem-search §6.)

Step 1: Real.structure bridge                              ~2-3 sessions
        Define `Real.structure` instance for Stdlib `R`.
        Required for any use of fourcolor `realplane`.

Step 2: Translate Ring → realplane region                  ~1-2 sessions
        `polygon_region : Ring -> region` and its
        boundary `polygon_border`.

Step 3: Seam 3 — edge_crosses_ray_correct                  ~1-2 sessions
        Linear algebra; independent of JCT.

Step 4: Seam 4 — degeneracy handling                       ~1-3 sessions
        Generic-position precondition or robust algorithm.

Step 5: Seam 2 — crossing → winding (or direct)            ~2-4 sessions
        Bridge the parity to interior membership.
        Most likely composed with Step 6 rather than
        proved standalone.

Step 6: Seam 5 — Jordan curve for simple polygons          ~thesis-scale
                                                           (unless library)
        The big one.  Either:
        (a) Port a JCT proof from a future library.
        (b) Prove it from scratch in fourcolor's
            realplane framework (3-5 months).

Step 7: Seam 6 — bounded-component identification          ~1-2 sessions
        Use closure + diameter to pick the bounded side.

Step 8: Seam 7 — composition                               ~1-2 sessions
        Chain everything into the biconditional.

Step 9: Tighten H1 to match point_in_ring_correct          ~½ session
        Add the ring_has_minimum_points precondition to
        H1's statement.  Re-derive
        overlay_ng_correct_conditional from the now-
        proven theorem (no longer conditional on H1).

Total (excluding Step 6 / Seam 5):   ~10-15 sessions
Total (including Step 6 if library lands):  ~12-18 sessions
Total (Step 6 from scratch):         ~3-5 months + the above
```

This is the Phase 5 roadmap for upgrading
`overlay_ng_correct_conditional` from H1-conditional to unconditional.

### Independent quick wins (do not wait for JCT)

Three pieces are tractable today and would strengthen the corpus
regardless of JCT progress:

  - **Step 0** (H1 internalisation via `realplane.region`) — ~1
    session.  Already flagged in
    `docs/ecosystem-search-2026-05-29.md` §6.
  - **Step 3** (`edge_crosses_ray_correct`) — 1-2 sessions.  Linear
    algebra only.  Adds a verified primitive that downstream consumers
    can use directly.
  - **Step 4** (`generic_ray_position` predicate + well-definedness
    lemma) — 1-2 sessions.  Documents the algorithm's actual contract
    rather than the idealised one.

Combined: 3-5 sessions for three Qed-closed deliverables that move the
seam map's "Missing" column to "Exists" for three of the seven seams.
None depend on JCT.

---

## §6 — State summary

| Seam | What | Exists | Missing | Cost | Library help |
|------|------|--------|---------|------|--------------|
| 1 | Algorithm → spec | `point_in_ring`, `ring_edges` | `geometric_interior` + connection | 1 sess. (def.) + JCT | fourcolor `realplane` (def. only) |
| 2 | Crossing → winding | `ring_simple` | Winding-number bridge | 2-4 sess. | NONE |
| 3 | Ray–segment correct | `edge_crosses_ray`, `cross_R_pt` | Correctness lemma | 1-2 sess. | NONE |
| 4 | Degeneracy | `ring_simple` (insufficient) | Generic-position / robust alg | 1-3 sess. | NONE |
| 5 | Simple polygon JCT | `ring_closed/simple/min` | Geometric JCT for R² | thesis-scale | fourcolor (combinatorial only) |
| 6 | Components → interior | (fourcolor `realplane`) | `Real.structure` bridge + ID | 3-5 sess. | fourcolor `realplane` |
| 7 | Composition | — | Chain seams 1-6 | 1-2 sess. | NONE |

**Headline numbers.**

  - Tractable without JCT (today): Seams 3 + 4 (+ Step 0
    internalisation).  ~3-5 sessions.
  - JCT-dependent (thesis-scale or library-dependent): Seams 2 + 5 + 6.
  - Final composition (Seam 7) once everything else lands: 1-2
    sessions.

**Deferred-registry status.**  `point_in_ring_correct` is NOT in
`docs/admitted-deferred-proofs.txt`.  There is no Coq Admitted to track
because `geometric_interior` has no Coq definition.  The gap is
recorded in `docs/audit-phase3-milestone5.md` §4.2 and (now) in this
document.  Once Step 0 (H1 internalisation) lands, the gap can be
re-stated as an Admitted and added to the registry.
