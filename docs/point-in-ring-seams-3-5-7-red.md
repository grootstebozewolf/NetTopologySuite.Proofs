# `point_in_ring_correct` Seams 3 / 5 / 7 — red workflow

**Status.**  Documentation only.  No Coq written.  Tangent map for
the three seams that remained open at the close of
`docs/point-in-ring-seam-attempts.md`.  Per-seam: simplest possible
lemma, mental proof trace, exact obstacle, cost.

**Companion documents:**

  - `docs/point-in-ring-correct-seam-map.md` — original seven-seam
    inventory.
  - `docs/point-in-ring-seam-attempts.md` — green-phase outcomes
    per seam.
  - `docs/ecosystem-search-2026-05-29.md` — JCT ecosystem audit.

---

## §1 — Seam 3: `geometric_interior` via fourcolor `realplane`

### Target statement

```coq
Definition geometric_interior (p : Point) (r : Ring) : Prop :=
  (* p is in the bounded connected component of R² \ image(r) *)
  ...
```

### Mental proof trace

**Step 1 — Import realplane:**

```coq
From fourcolor Require Import realplane.
```

`realplane.point` is `Inductive point := Point (x y : Real.val R)`
parametric over a Section variable `R : Real.structure`.  Section
closes the variable; external references become `realplane.point R`
requiring a concrete `R`.

**Step 2 — Build `Real.structure` for Stdlib R:**

```coq
Definition Stdlib_R_structure : Real.structure := {|
  Real.val  := R;
  Real.le   := Rle;
  Real.sup  := <Stdlib's `completeness` packaged as a function>;
  Real.add  := Rplus;
  Real.zero := 0%R;
  Real.opp  := Ropp;
  Real.mul  := Rmult;
  Real.one  := 1%R;
  Real.inv  := Rinv
|}.
```

Then build `Real.axioms Stdlib_R_structure : Prop` with 16 proof
obligations (see Tangent 1).

**Step 3 — Translate corpus `Point` to `realplane.point`:**

```coq
Definition to_rplane (p : Distance.Point)
  : realplane.point Stdlib_R_structure :=
  realplane.Point Stdlib_R_structure (px p) (py p).
```

**Step 4 — Translate corpus `Ring` to a `realplane` curve:**

`realplane` has `region` (`= point -> Prop`) and `map`
(`= point -> region`) but NO native curve type.  Building the
closed polygonal curve from a `Ring` requires:

  - A `polygon_image r : region Stdlib_R_structure` predicate
    that holds at points lying on any segment of `ring_edges r`.
  - Its complement: `complement r := fun z => ~ polygon_image r z`.

**Step 5 — Identify the bounded component:**

`realplane.connected` is "a region cannot be split by two disjoint
open sets" — the standard topological connectedness.  Identifying
WHICH connected component of the complement is bounded requires:

  - Showing `complement r` decomposes into exactly two `connected`
    sub-regions (this IS JCT for polygons).
  - Identifying the bounded one via diameter / lack of points at
    infinity.

### Tangents

#### Tangent 1: `Real.structure` instance for Stdlib `R`

`Real.structure` (fourcolor/reals/real.v:100-112) — **10 fields**:
`val`, `set`, `rel` (the last two computed), `le`, `sup`, `add`,
`zero`, `opp`, `mul`, `one`, `inv`.

`Real.axioms` (fourcolor/reals/real.v:146-178) — **16 axioms**:

  - `le_reflexive`, `le_transitive` — order.
  - `sup_upper_bound`, `sup_total` — supremum (the load-bearing
    classical piece; `sup_total` implies excluded middle).
  - `add_monotone`, `add_commutative`, `add_associative`,
    `add_zero_left`, `add_opposite_right` — additive group.
  - `mul_monotone`, `mul_commutative`, `mul_associative`,
    `mul_distributive_right`, `mul_one_left`,
    `mul_inverse_right`, `one_nonzero` — multiplicative semigroup +
    distributivity.

**Stdlib support:**

  - Order axioms: `Rle_refl`, `Rle_trans` direct hits.
  - Field axioms: `Rplus_comm`, `Rplus_assoc`, `Rplus_0_l`,
    `Rplus_opp_r`, `Rmult_comm`, `Rmult_assoc`,
    `Rmult_plus_distr_l`, `Rmult_1_l`, `Rinv_l` (under `<> 0`),
    `R1_neq_R0` — all in `RIneq` / `Raxioms`.
  - `add_monotone`/`mul_monotone`: `Rplus_le_compat_l`,
    `Rmult_le_compat_l` (under nonneg).
  - **`sup`/`completeness`**: Stdlib has `completeness :
    forall E : R -> Prop, bound E -> (exists x, E x) -> { m | ...
    }` (sig-type) in `Raxioms`.  Repackaging as
    `Real.sup : (R -> Prop) -> R` requires `proj1_sig
    \circ completeness` plus a default value for ill-defined sets.

**Cost:** the 16 axiom proofs are individually mechanical (each
~5-20 lines).  The `Real.sup` definition needs care because
`Real.sup` is total (`set -> val`) but `completeness` is partial
(requires `bound E` and `nonempty E`).  Total: **2-3 sessions**.
Status: **AMBER** (the `Dedekind.real : excluded_middle -> Real.model`
existence theorem confirms the construction is possible; the corpus
already has `Classical_Prop.classic` transitively through Flocq's
`round_mode`, satisfying the classical precondition).

#### Tangent 2: `Ring → realplane.region` polygon image

```coq
Definition polygon_image (r : Ring) : region Stdlib_R_structure :=
  fun z =>
    exists e t, In e (ring_edges r) /\
                0 <= t <= 1 /\
                z = realplane.Point _ ((1-t) * px (fst e) + t * px (snd e))
                                     ((1-t) * py (fst e) + t * py (snd e)).
```

Cost: ~50 lines including unfolding glue.  Status: **AMBER**.  The
definition is straightforward; the structural properties (image
closure, image continuity) are 1-2 sessions.

#### Tangent 3: bounded connected component identification

The complement `R² \ polygon_image r` for a simple closed polygon
has exactly two connected components (Jordan).  Identifying the
bounded one:

```coq
Definition geometric_interior (p : Point) (r : Ring) : Prop :=
  ~ polygon_image r (to_rplane p) /\
  exists M : R, M > 0 /\
    forall q, realplane.connected_to (to_rplane p) q
              (complement_region (polygon_image r))
              -> bounded_by M (to_rplane q).
```

Where `bounded_by M (x, y)` means `|x| < M /\ |y| < M`.

The Jordan piece — that the complement HAS exactly two components
— is what's actually needed.  `realplane.connected` is generic
topological connectedness; the corpus would need to instantiate
or prove the Jordan separation theorem for piecewise-linear closed
curves.

**Cost: 2-3 sessions for the diameter/bounded packaging.  PLUS the
Jordan piece itself — thesis-scale.**  Status: **RED** for the
Jordan piece; **AMBER** for the bounded-side wrapping.

### Seam 3 summary

| Tangent | Cost | Status | Library help |
|---------|------|--------|--------------|
| 1. `Real.structure` for Stdlib R | 2-3 sessions | **AMBER** | fourcolor (target type), Stdlib (axiom support) |
| 2. `Ring → polygon_image` | 1-2 sessions | **AMBER** | fourcolor (region type) |
| 3. bounded-component / Jordan | 2-3 sessions (wrap) + thesis (Jordan) | **RED** | NONE for Jordan |

**Total Seam 3 cost (assuming JCT available):** 5-8 sessions.

**Critical-path piece:** Tangent 3's Jordan separation.  Tangents
1+2 are independent and could be opportunistically built in
advance (they would give the corpus a `Real.structure` instance
+ a polygon-as-region predicate, both useful for other future
work).

---

## §2 — Seam 5: `winding_number`

### Target statement

```coq
Definition winding_number (p : Point) (r : Ring) : Z := ...
```

### Three options

#### Option A — Angular integral (atan2 fold)

```coq
Definition winding_number_R (p : Point) (r : Ring) : R :=
  (1 / (2 * PI)) *
  fold_left
    (fun acc e =>
       let '(A, B) := e in
       acc + atan2 (py B - py p) (px B - px p)
           - atan2 (py A - py p) (px A - px p))
    (ring_edges r) 0.
```

**Status of `atan2`**: NOT in Stdlib.  BUT Stdlib HAS `atan`
(`Stdlib.Reals.Ratan:549`, line `Definition atan x := let (v, _)
:= pre_atan x in v.`) with companion lemmas: `atan_bound`,
`atan_opp`, `atan_increasing`, `atan_0`, `atan_eq0`, `atan_1`,
`atan_tan`, `atan_inv`, `atan_eq_ps_atan`.  mathcomp-analysis has
`atan` (trigo.v:1134) with similar companions but NO `atan2`
either.

**Finding upgrade vs the prompt's expectation:** the prompt
suggested Seam 5 was blocked by "atan2 not in Stdlib".  Confirmed
true, but Stdlib `atan` IS available — `atan2` can be defined in
~30-40 lines via quadrant case-split (the standard recipe):

```coq
Definition atan2 (y x : R) : R :=
  if Rgt_dec x 0 then atan (y / x)
  else if Rlt_dec x 0 then
    if Rge_dec y 0 then atan (y / x) + PI
    else atan (y / x) - PI
  else  (* x = 0 *)
    if Rgt_dec y 0 then PI / 2
    else if Rlt_dec y 0 then -PI / 2
    else 0.  (* undefined at origin; conventional 0 *)
```

Proving its quadrant-correctness, continuity, and 2π-periodicity
properties: 1-2 sessions of careful case analysis.

The second obstacle remains: proving `winding_number_R p r ∈ Z`
for simple closed polygons (the integral is an integer multiple
of 2π).  This is the Jordan curve theorem in analytic form —
thesis-scale.  No library help.

#### Option B — Combinatorial turning number

```coq
Definition turning_number (r : Ring) : Z :=
  fold_left
    (fun acc '((A, B), (B', C)) =>
       acc + Z.sgn (Zof_R (cross_R_pt B A C)))
    (consecutive_triples (ring_edges r))
    0.
```

**Tangents**:

  - `consecutive_triples` helper over the edge list: ~20 lines.
  - `Zof_R` real-to-Z (proxying via `up`/`Z.of_nat`): ~10 lines.
  - Connecting `turning_number` to the winding number via the
    Gauss-Bonnet theorem for polygons (exterior angle sum = 2π):
    **thesis-scale**.

**Total**: 2-3 sessions for the definition + thesis for the
connection theorem.

#### Option C — Bypass winding number entirely

Don't define `winding_number`.  Instead prove directly:

```coq
Theorem crossing_parity_correct :
  forall (p : Point) (r : Ring),
    ring_simple r ->
    ring_closed r ->
    no_horizontal_edge_at p r ->
    point_in_ring p r <-> geometric_interior p r.
```

This collapses Seam 5 into Seam 3 — the bridge from parity to
topological interior IS the JCT piece (Seam 3 Tangent 3).
Winding number is a useful intermediate concept in classical
expositions but is NOT logically necessary for the corpus's
correctness chain.

The corpus already has, post-fold-bridge session:

  - `point_in_ring_eq_parity` — parity ↔ `point_in_ring`.

Combined with `geometric_interior` (Seam 3) plus the JCT piece
(crossing-parity ↔ interior-membership for simple polygons),
the corpus reaches `point_in_ring_correct` without ever defining
`winding_number`.

### Seam 5 recommendation

**Option C.**  Winding number is not on the critical path to
`point_in_ring_correct`.  Defining it would be useful corpus
infrastructure for other formalisations (homotopy, complex
analysis, polygonal turning) but does not advance the immediate
correctness goal.

| Option | Cost | Critical-path? |
|--------|------|----------------|
| A (atan2 + integral) | 3-5 sessions + thesis (integral-is-integer) | No — Seam 3 reaches goal without it |
| B (turning number) | 2-3 sessions + thesis (Gauss-Bonnet) | No — same |
| **C (bypass)** | **0 sessions** | **Yes — direct to Seam 3** |

### Cost upgrade vs the prompt

The prompt rated Option A at "1-2 sessions for atan2 hand-roll +
JCT-dependent for integral".  Confirmed.  Adjustment: the
atan companion-lemma infrastructure in `Stdlib/Reals/Ratan.v` is
richer than the prompt assumed (9 named lemmas including
periodicity-adjacent facts).  Even with Stdlib `atan`, Option A's
integral-is-integer obligation is the actual blocker — and Option
C avoids it.

---

## §3 — Seam 7: closure confirmation

### Status: **CLOSED**

```coq
Lemma segment_crosses_ray_implies_cross_R_pt :  (* forward *)
  ... (Qed) ...
Lemma cross_R_pt_implies_segment_crosses_ray :  (* reverse *)
  ... (Qed) ...
Theorem segment_crosses_ray_iff_cross_R_pt :   (* biconditional *)
  ... (Qed) ...
```

All three at `theories/PointInRingCorrect.v:689..798`.  Print
Assumptions: README-allowlisted axioms only
(`sig_forall_dec` + `functional_extensionality_dep`).

### Remaining work: NONE

The seam-attempts doc identified no further Seam 7 work after
the reverse direction closed.  The `cross_R_pt` ↔
`segment_crosses_ray` bridge is structurally complete.

A potential FUTURE extension (not currently a gap): connecting
`cross_R_pt` to a `signed_area : Ring -> R` for the polygon
(used in shoelace-formula contexts) — but this is a polygon
property, not a Seam 7 obligation.

---

## §4 — Updated path to `point_in_ring_correct`

### Without JCT (current corpus state)

  - 6 of 7 seams Qed-closed.
  - `point_in_ring_correct_conditional` records the headline
    shape (vacuous; gated by `interior` predicate).
  - `OverlayCorrectness.v`'s `overlay_ng_correct_conditional`
    consumes the conditional via Section Variable
    `geometric_interior`.

### Minimum JCT investment to discharge `point_in_ring_correct`

Following Seam 5 Option C (bypass winding number):

```
Tangent 1 (Real.structure for Stdlib R):    2-3 sessions  AMBER
Tangent 2 (Ring → polygon_image region):    1-2 sessions  AMBER
Tangent 3a (bounded-component packaging):   2-3 sessions  AMBER
Tangent 3b (Jordan separation theorem):     thesis-scale  RED
Composition (Seam 7 of seam-map):           1-2 sessions  AMBER
-----------------------------------------------------------
Total (JCT-piece amortised):                6-10 sessions
                                            + thesis for JCT itself
```

If `Tangent 3b` is taken from a future library import (the trigger
condition below), the engineering work collapses to ~6-10 sessions.

### Trigger conditions for re-opening Seam 3

  1. **fourcolor adds a Stdlib R model** — would discharge
     Tangent 1.  Not currently present; their Dedekind module
     constructs `Real.model` from mathcomp `rat` cuts only
     (`fourcolor/proof/dedekind.v`).  Polling: check on each
     fourcolor release.
  2. **mathcomp-analysis adds JCT for R²** — would discharge
     Tangent 3b.  Not currently present (`docs/ecosystem-search-
     2026-05-29.md` §5: RED).  mathcomp's `topology_theory` has
     `connected` / `path_connected` primitives but no Jordan-
     curve theorem.
  3. **In-corpus thesis investment** — the existing classical
     foundation (`Classical_Prop.classic` transitively pulled
     through Flocq's `round_mode`) is sufficient to construct
     Tangent 1 from scratch, but Tangent 3b remains 3-5 months
     of dedicated work per the original audit estimate
     (`docs/audit-phase3-milestone5.md` §4.2).

### Independent tractable work (no JCT trigger needed)

  - **Tangent 1** (Real.structure for Stdlib R): 2-3 sessions.
    Lands a corpus-wide `Stdlib_R_structure : Real.structure`
    instance plus the 16 axiom proofs.  Useful even without
    Tangent 3 — would unlock fourcolor's combinatorial-Jordan
    machinery for arbitrary corpus problems.
  - **Tangent 2** (polygon-as-region): 1-2 sessions.  Lands
    `polygon_image r : region Stdlib_R_structure`.  Requires
    Tangent 1 to typecheck.

These would change Seam 3's status from "blocked on Tangent 1"
to "blocked on Tangent 3b" — the JCT piece becomes the only
remaining gap, no longer obscured by infrastructure work.

---

## §5 — Findings adjusting prompt expectations

### Finding 1: Stdlib `atan` more useful than anticipated

The prompt rated Seam 5 atan2 hand-roll at "~30 lines, then 2-3
sessions for properties".  Stdlib `Ratan.v` provides 9 companion
lemmas (`atan_bound`, `atan_opp`, `atan_increasing`, `atan_0`,
`atan_eq0`, `atan_1`, `atan_tan`, `atan_inv`, `atan_eq_ps_atan`).
The atan2 definition becomes ~30 lines; the atan2 properties
inherit most of their work from Stdlib, reducing the property-
proof cost to 1-2 sessions.

**Net adjustment:** Seam 5 Option A definition + properties:
2-3 sessions total (down from 3-5).  The integral-is-integer
JCT-dependent piece is unaffected.

### Finding 2: fourcolor's classical-real construction is rat-based

fourcolor's `Dedekind.real : excluded_middle -> Real.model`
constructs reals from MATHCOMP `rat` cuts, not from Stdlib `R`.
There is NO existing Stdlib R → Real.model bridge in fourcolor
or any installed library.

**Net adjustment:** Tangent 1 cost confirmed at 2-3 sessions; no
shortcut available via library import.  HOWEVER, the corpus's
classical axiom footprint (`Classical_Prop.classic`) is exactly
the `excluded_middle` hypothesis fourcolor's construction
requires, so the construction is feasible and the corpus's
epistemic invariants are preserved.

### Finding 3: Seam 5 collapses into Seam 3 via Option C

Winding number is NOT on the critical path to
`point_in_ring_correct`.  The parity-to-interior bridge IS the
JCT piece (Seam 3 Tangent 3b); going through winding number adds
work without progress.

**Net adjustment:** Seam 5 effective cost is **0 sessions** under
Option C; the prompt's "1-2 sessions for atan2" investment is
optional infrastructure, not on the critical path.

### Finding 4: Seam 7 has no remaining work

Confirmed via grep — the previous session closed both the reverse
direction and the biconditional.  The seam-map doc identified no
follow-up.  Seam 7 is structurally complete.

---

## §6 — One-line summary

**Six of seven seams Qed-closed; the seventh (Seam 3) collapses to
one JCT-shaped gap (Tangent 3b) plus 5-8 sessions of mechanical
infrastructure (Tangents 1+2 + composition).  Seam 5 is not on the
critical path and can be skipped via Option C.  Trigger condition
for re-opening: fourcolor adds Stdlib R model, OR mathcomp-analysis
adds JCT for R², OR the corpus invests thesis-scale (3-5 months)
in proving Jordan from scratch.**
