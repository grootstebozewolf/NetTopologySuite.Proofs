# Library audit: OverlayNG correctness for Phase 3

**Question.** To formalise OverlayNG's correctness theorem
(`overlay_ng_correct` — boolean operations on polygonal geometries),
what's reusable from Phase 0/1/2, what concepts are missing from the
corpus, and what is the proof chain that connects existing
infrastructure to the final theorem?

**Decision driver.** Phase 2 closed the snap-rounding piece
conditionally on `hobby_lemma_4_3`. The four endpoint files
(`HobbyTheorem_b64.v`, `TopologicalCorrectness_b64.v`,
`SnapRounding_b64.v`, `HotPixel_b64.v`) give Phase 3 its Stage-1
"noding is correct" entry point. Phase 3 builds on top of that:
Stages 2 and 3 of OverlayNG — the planar topology graph and the
result-extraction traversal — are combinatorial / set-theoretic and
sit outside the arithmetic regime that Phases 0–2 established.

**Discipline note.** This is a read-only audit. No Coq is written
in the session that produces this document. The audit fixes scope
for subsequent milestones; Milestone 1 (definitions of
`valid_geometry` and `boolean_op`) is the first session that
introduces `.v` files for Phase 3.

---

## §1. What OverlayNG does, and why NTS needs it

**Input.** Two geometries `A`, `B` (typically polygons or
multi-polygons) and a boolean operator `op ∈ {Union, Intersection,
Difference, SymDiff}`.

**Output.** A geometry `overlay_ng op A B` whose point set equals
`boolean_op op A B` and that is itself a valid geometry under OGC
Simple Features Access (06-103r4 §6).

**Algorithm.** Three stages:

1. **Noding** — Snap-round all input edges, then find every
   intersection. Insert intersection vertices to produce a
   fully-intersected arrangement. Phase 2 closed this stage
   conditionally on `hobby_lemma_4_3`.
2. **Topology graph** — Convert the noded edge set into a planar
   graph. Each edge carries a label indicating which input
   geometry (`A`, `B`, or both) contributed it, plus which side of
   the edge is interior to `A` / `B`.
3. **Result extraction** — Traverse the labelled graph using
   `op`-specific selection rules. Reassemble polygons (rings →
   shells + holes) and emit the result geometry.

**Why NTS needs a formalisation.** OverlayNG is the entry point to
nearly every spatial operation a GIS user runs. Bugs in the
overlay layer manifest as the worst failure mode in computational
geometry: silently wrong topology that's only detected when a
downstream consumer chokes on a degenerate output. The Java/C# code
has accumulated robustness fixes over ~20 years; a machine-checked
correctness theorem fixes the algorithm against a precise
specification rather than against the regression test suite.

**The correctness theorem (informal).**

> If `A` and `B` are valid geometries, then `overlay_ng op A B` is
> valid and its point set equals `boolean_op op A B`.

**The correctness theorem (target Coq shape).**

```coq
Theorem overlay_ng_correct :
  forall (A B : Geometry) (op : BooleanOp),
    valid_geometry A ->
    valid_geometry B ->
    valid_geometry (overlay_ng op A B) /\
    point_set (overlay_ng op A B) = boolean_op op A B.
```

`Geometry`, `BooleanOp`, `valid_geometry`, `point_set`,
`boolean_op`, and `overlay_ng` are all Phase 3 deliverables. They
do not exist in the corpus today.

---

## §2. The four-link proof chain

The theorem decomposes into four linked obligations. Each link
corresponds to one stage of the algorithm or one bridge between
stages.

**Link 1 — Input validity ⇒ noding correctness.**

```
valid_geometry A → valid_geometry B →
  fully_intersected (noded_segments A B)
```

Cites `hobby_theorem_4_1_conditional`
(`theories-flocq/HobbyTheorem_b64.v:159`). The Phase 2 endpoint is
conditional on `hobby_lemma_4_3`; Phase 3 either inherits the
conditional or waits on the lemma's closure (4–6 weeks of focused
work, registered in `docs/admitted-deferred-proofs.txt`).

**Link 2 — Noding ⇒ valid topology graph.**

```
fully_intersected segs →
  valid_topology_graph (build_graph segs)
```

New. No analogue exists in the corpus. Estimated scope: 2–3
sessions. Should survey `coq-community` / `mathcomp` for planar
graph infrastructure before defining from scratch.

**Link 3 — Valid graph ⇒ correct labelling.**

```
valid_topology_graph g →
  correct_labels op g
```

New. Encodes the JTS / GEOS labelling-rule machinery. Estimated
scope: 2–3 sessions once the graph representation is fixed.

**Link 4 — Correct labelling ⇒ validity + point-set equality.**

```
correct_labels op g →
  valid_geometry (extract op g) ∧
  point_set (extract op g) = boolean_op op A B
```

The set-theoretic heart of the theorem. Estimated scope: 6–10
sessions. This is the thesis-shaped link of Phase 3 — see §5.

**Composition.** Links 1–4 compose into `overlay_ng_correct` by
straightforward sequencing once each is closed. Phase 3 can ship
the composition skeleton early (as a chain of `Admitted` lemmas
matching the link shapes) and discharge the links incrementally.

---

## §3. Corpus infrastructure from Phases 0–2

Phase 3 inherits a substantial arithmetic and combinatorial base.
Every result below is `Qed`-closed except where flagged.

### §3.1 Phase 0 — orient2d predicate

- `b64_orient_sign_exact_sound`
  (`theories-flocq/Orient_b64_exact.v:89`).
- `b64_orient_sign_stage_d_sound`
  (`theories-flocq/Orient_b64_stage_d.v:143`) — Shewchuk-cascade
  arithmetic filter; correct sign of the exact determinant on
  `binary64` inputs. Cites Shewchuk 1997.
- `b64_orient_sign_stage_d_tiny_regime_decisive`
  (`theories-flocq/Orient_b64_stage_d.v:170`).
- `b64_ozaki_filter_sound` — Ozaki γ₂ filter, same interpretation,
  tighter threshold. Cites Ozaki et al. 2012 and the Fortune–Van
  Wyk 1996 §4.1 static error bound framework.

**Phase 3 role.** Orientation is the discriminator that decides
which side of an edge a point lies on — central to Link 3
(labelling correctness) and to ring-orientation checks in
`valid_geometry`.

**Deferred dependency.** `fast_expansion_sum_nonoverlap_shewchuk`
(Shewchuk Theorem 13) is the only `Admitted` entry under the
orient2d predicate. It is the load-bearing piece for
`orient2d_exact`'s headline. Estimated scope: 3–4 sessions
(Route 2 list-indexing invariant; see
`docs/shewchuk-theorem-13-proof-structure.md`). **Does not gate
Phase 3** — Stage D is the active orient2d path; the exact-cascade
headline is a separate strengthening.

### §3.2 Phase 1 — intersection coordinates

- `b64_intersect_den_forward_error`
  (`theories-flocq/Intersect_b64_exact.v:1088`).
- `b64_intersect_s_forward_error` (:1329).
- `b64_intersect_mult_x_forward_error` (:1482).
- `HasIntersect_sound` — coordinate error bound `K·eps` under
  `coord_int_safe`. Cites Fortune–Van Wyk 1996 Figure 3 operation
  counts.

**Phase 3 role.** When two segments cross, Stage 1 needs to know
the intersection coordinate to within a hot-pixel radius. Phase 1
gives the bound; Phase 2 uses it inside the snap-rounding
correctness chain.

### §3.3 Phase 2 — snap-rounding foundation

**`theories-flocq/HobbyTheorem_b64.v`.**
- `hobby_theorem_4_1_conditional` (:159) — `Qed`-closed,
  conditional on `hobby_lemma_4_3`. Direct entry point for Phase 3
  Link 1.
- `hobby_lemma_4_2` (:108) — `Admitted`. Monotone-coordinate
  lemma. Registered, 2–3 sessions estimated.
- `hobby_lemma_4_3` (:130) — `Admitted`. Piecewise-linear
  ordering. Registered, 4–6 weeks estimated (thesis-shaped).

**`theories-flocq/TopologicalCorrectness_b64.v`.**
- `snap_round_preserves_shared_hot_pixel` (:107).
- `b64_snap_round_preserves_shared_hot_pixel` (:118).
- `b64_snap_round_preserves_pixel_cover` (:145).

**`theories-flocq/SnapRounding_b64.v`.**
- `snap_round_idempotent` (:94).
- `snap_round_preserves_passes_through` (:108).
- `b64_snap_round_preserves_passes_through` (:175).
- `b64_snap_round_segment_correct` (:205).

**`theories-flocq/HotPixel_b64.v`.**
- `b64_in_hot_pixel_sound` (:607).
- `b64_segment_touches_hot_pixel_sound` (:781).
- `b64_segment_touches_hot_pixel_endpoints_sound` (:824).
- `b64_passes_through_sound` (:2438) / `_complete` (:2422).

**`theories-flocq/PassesThroughHalfopen_b64.v`.**
- `b64_passes_through_hot_pixel_halfopen_sound` (:441).
- `b64_passes_through_hot_pixel_halfopen_complete` (:458).
- `b64_passes_through_hot_pixel_halfopen_implies_closed` (:479).

**Oracle channel.** 690/690 tests green end-to-end against the
oracle binary (Phase 0+1: 671; Phase 2: +19). Boundary divergence
between closed-pixel and half-open-pixel conventions is empirically
witnessed; a formal Coq witness is deferred and is **not** on the
Phase 3 critical path.

### §3.4 R-side and general infrastructure (`theories/`)

- `theories/Orientation.v` — R-side orient predicate (`Reflection`
  bridge target).
- `theories/Intersect.v` — R-side intersection predicate.
- `theories/HotPixel.v` — R-side hot-pixel data structure.
- `theories/Segment.v` — segment-level basic facts.
- `theories/LineEq.v`, `theories/Lattice.v`, `theories/LexOrder.v` —
  utility layers Phase 3 may need for graph orderings.
- `theories/Polynomial.v`, `theories/Real.v`, `theories/Reflection.v`
  — R-side foundations.

**Phase 3 role.** The R-side `Orientation` / `Intersect` /
`HotPixel` predicates are the natural specifications that Phase 3's
graph and labelling machinery should phrase itself against; the
`b64_*` layer is what Phase 3 actually computes with via the
existing Reflection bridge.

### §3.5 What Phase 3 cannot reuse

There are **no overlay-shaped definitions** in the corpus today. A
grep for `overlay`, `OverlayNG`, `boolean_op`, `planar_graph`,
`topology_graph` turns up only two doc-comment mentions in
`theories/Segment.v:8` and `theories/Intersect.v:5` (forward
references to overlay work that Phase 2 set up). Phase 3 is
**greenfield** on the graph and result-extraction side.

---

## §4. Missing concepts — the genuine Phase 3 scope

Six concepts have to be introduced before the four-link chain can
be stated, let alone proved.

### §4.1 `valid_geometry`

Source: OGC 06-103r4 §6 (verified against the primary source by
the project owner — see §7 for the attribution note).

```coq
Definition valid_geometry (g : Geometry) : Prop :=
  rings_closed g /\
  no_self_intersections g /\
  holes_inside_shells g /\
  no_duplicate_rings g /\
  consistent_orientation g.
```

**Scope.** 1–2 sessions. Definitional. Reuses
`theories/Orientation.v` and `theories/Intersect.v` for the
sub-predicates.

**Dependencies.** None outside the existing R-side modules. No
Flocq.

### §4.2 `boolean_op` (mathematical reference)

```coq
Definition boolean_op (op : BooleanOp)
    (A B : Geometry) : PointSet :=
  match op with
  | Union        => point_set A ∪ point_set B
  | Intersection => point_set A ∩ point_set B
  | Difference   => point_set A \ point_set B
  | SymDiff      => (point_set A \ point_set B) ∪
                    (point_set B \ point_set A)
  end.
```

**Scope.** 1 session. Pure set theory. The hard piece here is
`point_set : Geometry → R² → Prop`, which is a recursive walk over
shells / holes / multi-components. No Flocq.

### §4.3 Planar topology graph

Stage 2 of OverlayNG operates on a planar embedded graph with
labelled edges. The corpus has no graph theory yet.

```coq
Record EdgeLabel := {
  in_A    : bool;
  in_B    : bool;
  side_A  : Side;   (* In, Out, On *)
  side_B  : Side;
}.

Record TopologyGraph := {
  nodes  : list Point;
  edges  : list (Point * Point * EdgeLabel);
  faces  : list Face;   (* derived after traversal *)
}.

Definition valid_topology_graph (g : TopologyGraph) : Prop := ...
```

**Scope.** 2–3 sessions to define and prove basic structural
properties (well-formedness, edge incidence, face existence).

**Survey before building.** `coq-community` (`coq-graph`,
`hierarchy-builder` ecosystem) and `mathcomp` (`finmap`, `finset`,
`fingraph`) may provide reusable planar / finite graph machinery.
Spending the first session of Milestone 2 on a vendor / build call
is the right move.

### §4.4 Labelling rules

The per-operator rules that say which edges of the graph belong to
the result. From the JTS / GEOS implementation:

| op            | Edge selected when                       |
|---------------|------------------------------------------|
| Union         | `in_A ∨ in_B` and not interior-to-both   |
| Intersection  | `in_A ∧ in_B` (boundary or shared edges) |
| Difference    | `in_A ∧ ¬in_B` (boundary of A outside B) |
| SymDiff       | XOR with consistency conditions          |

**Scope.** 2–3 sessions once §4.3 is in place. Algorithm-specific;
derived from `OverlayNG.java` / `OverlayLabeller.java` in JTS.

### §4.5 Noding-to-graph bridge

```coq
Theorem noding_produces_valid_graph :
  forall (segs : list (BPoint * BPoint)),
    fully_intersected (snap_round_segments segs) ->
    valid_topology_graph
      (build_graph (snap_round_segments segs)).
```

The connector between Link 1 (Phase 2's endpoint) and Link 2
(graph well-formedness). Cites `hobby_theorem_4_1_conditional`.

**Scope.** 3–4 sessions. Builds a finite graph from a finite,
fully-intersected segment list and proves every edge / vertex is
well-formed.

### §4.6 Set-theoretic correctness (Link 4)

The bridge between graph traversal and point-set boolean
operations. The thesis-shaped piece of Phase 3 — see §5.

**Scope.** 6–10 sessions.

---

## §5. The thesis-shaped piece — Link 4

Link 4 is qualitatively different from Links 1–3. Links 1–3 are
combinatorial: they reason about finite structures (segments,
vertices, edges, labels) under well-defined transformations. Link
4 is set-theoretic: it has to show that a finite, discrete graph
encoding correctly represents an uncountable set of points in R².

**Statement.**

```coq
Theorem extract_set_correctness :
  forall (op : BooleanOp) (A B : Geometry) (g : TopologyGraph),
    valid_topology_graph g ->
    correct_labels op g ->
    g = build_graph (noded_segments A B) ->
    point_set (extract op g) = boolean_op op A B.
```

**Why it's harder.** The four obligations stack:

1. The interior of every face of `g` is uniformly inside-A /
   outside-A and uniformly inside-B / outside-B (the labelling
   classifies a 2D continuum from a 1D edge classification).
2. The boundary of `extract op g` lies on edges of `g` (no
   "phantom boundary" off the noded arrangement).
3. Holes are correctly nested inside shells in the output (a global
   ring-orientation argument, not local).
4. Snap-rounding's bounded-displacement guarantee (Phase 2 §2.5,
   not currently in the corpus) controls the metric distance
   between `extract op g` and the mathematical
   `boolean_op op A B`. If the metric error is left implicit, the
   theorem holds only "topologically" — Phase 3 has to make a
   precise call here.

**Machinery needed.** Jordan curve theorem variants for piecewise
linear curves; ring-winding-number arguments; possibly the
classification of plane components as inside / outside a closed
curve. None of this is in the corpus, and `mathcomp` /
`coq-community` do not (as of 2026-05) have a directly reusable
plane topology library. This link is the natural place for the
corpus to acquire a small planar-topology kernel.

**Strategic question.** Phase 3 has the option of stating Link 4
"modulo a bounded-displacement constant" — accepting that the
output matches `boolean_op` up to snap-rounding's metric error
rather than exactly. The exact statement requires either
proving the bounded-displacement theorem (Phase 2's §2.5 — not
landed) or pinning a `Parameter` constant (corpus-invariant
violation). Milestone 5 begins with this decision.

---

## §6. Milestone structure

| Milestone | Deliverable                                  | Estimate     |
|-----------|----------------------------------------------|--------------|
| M1        | `valid_geometry` + `boolean_op` definitions  | 1–2 sessions |
| M2        | Planar topology graph representation         | 2–3 sessions |
| M3        | Noding-to-graph bridge (Links 1+2)           | 3–4 sessions |
| M4        | Labelling correctness (Link 3)               | 2–3 sessions |
| M5        | Set-theoretic correctness (Link 4)           | 6–10 sessions|
| **Total** |                                              | **14–22 sessions** |

**Milestone gating.**
- M1 has no Phase 3 prerequisite — can start immediately after
  this audit lands.
- M2 should begin with a one-session survey of `coq-community` /
  `mathcomp` for reusable graph infrastructure.
- M3 inherits Phase 2's conditional. If `hobby_lemma_4_3` lands
  before M3, Link 1 becomes unconditional; otherwise M3 ships
  conditional Link 1.
- M5 begins with the strategic call described in §5 (exact vs.
  bounded-displacement statement).

**What's not on the critical path.**
- `fast_expansion_sum_nonoverlap_shewchuk` (Shewchuk Thm 13). Phase
  3 uses Stage D, not the exact cascade.
- `hobby_lemma_4_2`. Independent of Link 1 — it supports a
  different Phase 2 lemma.
- The full boundary-divergence Coq witness from Phase 2's oracle
  channel work. Empirical witness suffices for Phase 3.

---

## §7. Bibliography

Only papers verified against primary sources during the engagement
that produced this audit doc.

**Shewchuk (1997)** — "Adaptive Precision Floating-Point Arithmetic
and Fast Robust Geometric Predicates," *Discrete & Computational
Geometry* 18(3):305–363.
- Corpus role: Phase 0 Stage D arithmetic cascade.
- Phase 3 role: orient2d predicate foundation underlying Link 3
  labelling discriminators.

**Hobby (1999)** — "Practical Segment Intersection with Finite
Precision Output," *Computational Geometry: Theory and
Applications* 13(4):199–214.
- Corpus role: Phase 2 endpoint (`HobbyTheorem_b64.v`).
- Phase 3 role: Link 1 noding correctness.
- Open dependencies: `hobby_lemma_4_2` (2–3 sessions),
  `hobby_lemma_4_3` (4–6 weeks, thesis-shaped); both registered in
  `docs/admitted-deferred-proofs.txt`.

**Fortune and Van Wyk (1996)** — "Static Analysis Yields Efficient
Exact Integer Arithmetic for Computational Geometry," *ACM
Transactions on Graphics* 15(3):223–248.
- Corpus role: background analysis confirming Phase 0/1
  arithmetic bounds; §4.1 static-error-bound formula and Figure 3
  operation counts.
- Phase 3 role: bit-length bounds for predicate arguments inside
  graph-edge classification.

**Ozaki, Ogita, Rump, Oishi (2012)** — "Tight and Efficient
Enclosure of Matrix Multiplication by Using Optimized BLAS,"
*Numerical Linear Algebra with Applications* 18(2):237–248. (The
γ₂ filter analysis appears in the companion line of work by the
same group.)
- Corpus role: Phase 0 `b64_ozaki_filter_sound`.
- Phase 3 role: alternative orient2d filter; same logical role as
  Shewchuk Stage D.

**OGC 06-103r4** — *OpenGIS Implementation Standard for Geographic
Information — Simple Feature Access — Part 1: Common Architecture,*
v1.2.1.
- Phase 3 role: source of the `valid_geometry` definition (§6 of
  the standard).
- **Attribution note (project-owner verified).** The curve types
  `CIRCULARSTRING`, `COMPOUNDCURVE`, `CURVEPOLYGON` are **SQL/MM
  Spatial (ISO/IEC 13249-3) constructs, not OGC SFA**.
  `TRIANGLE`, `MULTICURVE`, `MULTISURFACE` *are* in SFA. This
  attribution was checked against the primary documents; do not
  regenerate it from secondary sources.

**JTS / GEOS source (referenced as algorithm specification, not
peer-reviewed publication).** The labelling rules in §4.4 and the
result-extraction traversal in §4.6 derive from `OverlayNG.java`
in the JTS Topology Suite. The Coq formalisation specifies the
algorithm; correctness is judged against `boolean_op`, not against
JTS's implementation.

---

## §8. Resumption checklist

A future contributor picking up Phase 3 from cold:

- [ ] Read this document end-to-end.
- [ ] Read `docs/hobby-theorem-proof-structure.md` for Phase 2's
      conditional structure.
- [ ] Read `theories-flocq/HobbyTheorem_b64.v` to confirm Link 1's
      entry point shape.
- [ ] Read `theories-flocq/TopologicalCorrectness_b64.v` for the
      "snap-round preserves X" pattern that Link 2 will mirror.
- [ ] Check `docs/admitted-deferred-proofs.txt` — the two Hobby
      lemmas remain open; estimate whether closing
      `hobby_lemma_4_3` before M3 changes Phase 3's plan.
- [ ] Survey `coq-community` and `mathcomp` for planar / finite
      graph theory **before** defining `TopologyGraph` from
      scratch. One session of vendor / build call.
- [ ] Draft `valid_geometry` against OGC 06-103r4 §6 read from the
      primary PDF. Do not trust the curve-type attribution from
      training data or from secondary sources — see §7.
- [ ] State the Milestone 1 theorem
      (`valid_geometry_round_trip`?) before writing the first
      `.v` file. Treat the audit doc as the spec.
- [ ] Decide on the Link 4 statement form (exact vs.
      bounded-displacement) before starting M5. Document the
      decision in this file's §5.

---

## §9. Audit summary

- **Reused from Phase 0/1/2:** orient2d (Stage D + Ozaki),
  intersection coordinate bound, full snap-rounding foundation
  (`hobby_theorem_4_1_conditional`), hot-pixel machinery, R-side
  predicate library. Substantial — Phase 3 does not redo any
  arithmetic or snap-rounding work.
- **Vendored:** to be decided in M2 first session — planar / finite
  graph machinery from `coq-community` or `mathcomp` if a clean
  reuse target exists.
- **Built:** `valid_geometry`, `boolean_op`, `TopologyGraph`,
  labelling rules, noding-to-graph bridge, Link 4 set-theoretic
  correctness. Five out of six are combinatorial / definitional;
  Link 4 is the thesis-shaped piece.
- **Character of the work:** combinatorial and set-theoretic.
  Phase 3 is qualitatively different from Phases 0/1
  (sign-correctness of arithmetic expressions) and similar in
  shape to Phase 2's `topological correctness` slice — graph and
  set theory replace hot-pixel combinatorics, but the overall
  research-shaped flavour carries through.
- **Corpus invariant:** maintained. M1–M4 plan to ship Qed-closed.
  M5 (Link 4) may require either closing the bounded-displacement
  theorem first or restating Link 4 modulo a metric error — both
  acceptable; pinning a `Parameter` constant is not.
- **Critical-path dependencies on registered Admitted entries:**
  `hobby_lemma_4_3` only (and only inherits the conditional shape;
  doesn't block Phase 3 progress).

Phase 3 is a **multi-month engagement** comparable in scope to
Phase 2. The composition skeleton (the four-link chain stated as
`Admitted` lemmas) can ship inside M1; the actual discharge
proceeds through M2–M5 incrementally.
