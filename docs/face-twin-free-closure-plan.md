# `face_twin_free` closure plan

*Session: `claude/dcel-seams-env-setup-11ec9n` (2026-06-16).*

This document plans the remaining work on the `face_twin_free` seam, taking
into account the seam-closing that has already landed in the corpus. The
short version: **`face_twin_free` itself is no longer the gap.** It is fully
reduced, by `Qed` lemmas, to a stack of *named hypotheses* carried by the
headline `extract_rings_valid`. The residual work is discharging those
hypotheses — primarily the **planar Euler identity** and **2-edge-connectivity**
of the noded arrangement — from arrangement formation.

## 1. Current state — the chain is closed (conditionally)

The per-face `face_twin_free` obligation is discharged end-to-end. Reading the
chain downward from the headline:

| Step | Lemma (file) | Status |
|------|--------------|--------|
| `extract_rings_valid` | `theories-flocq/OverlayBridge.v:490` | conditional **Qed** |
| ← `extract_faces_valid_sep` | `theories/FaceOrbitSep.v:174` | **Qed** |
| ← `face_twin_free_of_sep` | `theories/FaceOrbitSep.v:154` | **Qed** |
| ← `extract_faces_valid_twin_aware` | `theories/FaceTwinAware.v:292` | **Qed** |
| `twins_in_different_faces` ← `H_bridge_well_noded` / `edge_2_connected_twins_sep` | `theories/EdgeFaceBridge.v:1484` / `:1465` | **Qed** |
| `H_bridge_premise` ← `H_bridge_premise_from_euler` | `theories/HBridgeEuler.v:42` | **Qed** |
| face delta `num_faces (E_minus E e) = num_faces E + 1` ← `num_faces_E_minus_splice` | `theories/NumFacesSplice.v:43` | **Qed** |
| Euler→disconnect ← `H_bridge_core_conclusion_from_euler` | `theories/EulerBridge.v:133` | **Qed** |

Key reductions, in words:

- **`face_twin_free_of_sep`** turns the *per-face* predicate
  `face_twin_free D d (face_period D d)` (no dart of a face walk appears with
  its twin) into a single *global* orbit condition
  `twins_in_different_faces D` (no dart shares an `fstep`-orbit with its twin),
  using that the period walk enumerates the face orbit
  (`walk_at_period_iff_same_face`) and that `same_face` is an equivalence on an
  `arrangement_ok` set.
- **`edge_2_connected_twins_sep`** discharges `twins_in_different_faces` from
  graph 2-edge-connectivity: contrapositively, a dart sharing a face with its
  twin makes the carrier edge a *cut edge* (`same_face_twin_is_cut`), so a
  2-edge-connected `E` has no such dart. The two structural obstructions are
  the **antenna** (degree-1 tip — excluded by `no_spurs`) and the **dumbbell**
  (a bridge with no leaf — excluded by `edge_2_connected`).
- **`H_bridge_premise_from_euler`** supplies the one genuinely planar fact the
  cut-edge argument needs (removing a same-face edge *disconnects* rather than
  merely splits a face) from the planar Euler identity `V + F = E + 2·C`.

The deferred-proof registry (`docs/admitted-deferred-proofs.txt`) is **empty**;
there is no `Admitted` anywhere on this path. See `docs/extract-faces-bridge.md`
§§19–22 for the history.

## 2. The residual seam — named hypotheses of `extract_rings_valid`

Everything above is parametric over the hypotheses `extract_rings_valid`
carries (`OverlayBridge.v:490`). Writing `E := result_edges op (noded_labeled_graph A B)`:

| # | Hypothesis | Provenance today | Status |
|---|-----------|------------------|--------|
| H1 | `well_noded_darts E` | noding correctness | largely established |
| H2 | `no_spurs (result_darts …)` | noding correctness | largely established |
| H3 | `edge_2_connected E` | **carried (irreducible)** — dumbbell shows it's not derivable; equivalence to `twins_in_different_faces` proven both ways (2026-06-16); `*_sep` headline variants carry the equivalent directly | **resolved** |
| H4 | `NoDup E` | **DERIVED** from the noding construction (`OverlayBridge.NoDup_result_edges_noded` via `merge_NoDup_keys`) | **DONE (2026-06-16)** |
| H5 | `euler_characteristic E` | **carried** | **open (deep)** |
| H6 | `∀ e ∈ E, euler_characteristic (E_minus E e)` | **carried** | **open (deep)** |
| H7 | `∀ e ∈ E, num_vertices (E_minus E e) = num_vertices E` | **DERIVED** from `no_spurs` + `well_noded_darts` (`VertexDegree.num_vertices_E_minus_eq`) | **DONE (2026-06-16)** |

`euler_characteristic` is `num_vertices E + num_faces E = num_edges E + 2 *
num_components E` (`EulerArrangement.v:76`), the subtraction-free genus-0 Euler
relation for the combinatorial map (rotation system). The `2·C` (not `1+C`) is
deliberate: the bridge argument's `E_minus` side is *disconnected*, and the
identity must survive that.

## 3. Discharge plan, by hypothesis

### H7 — vertex invariance under edge deletion *(DONE — 2026-06-16)*

**Landed** in `theories/VertexDegree.v` (`num_vertices_E_minus_eq`) and wired
into `H_bridge_premise_from_euler`; the hypothesis is dropped from
`extract_rings_valid` / `extract_rings_valid_holes` / `valid_geometry_extract`.
The proof: `no_spur_fan_has_other` (every vertex has an outgoing dart other than
the edge's reversal — else the face step is a spur, via `next_in`), plus
`at_most_one_carrier_at_vertex` (the two darts of a proper edge sit at its two
distinct endpoints), give the reverse inclusion `verts E ⊆ verts (E_minus E e)`;
equality follows by antisymmetry against the existing `num_vertices_E_minus_le`.

Original goal: `∀ e ∈ E, num_vertices (E_minus E e) = num_vertices E`.

`num_vertices_E_minus_le` (`EulerArrangement.v:124`) already gives `≤`. The
reverse needs: deleting one edge `e = (u, v)` drops no vertex, i.e. both `u`
and `v` remain endpoints of some surviving edge. This is exactly **minimum
degree ≥ 2**, which follows from `no_spurs`: `no_spurs` is "no degree-1
vertex / no leaf" (`FaceOrbitSep.v:13`; `fstep d = twin d` iff `outgoing
(dtip d) D = {twin d}`, a leaf head). 

Concrete steps (all `theories/`-only, pure list/Point combinatorics):
1. Lemma `no_spurs_min_degree_2`: `no_spurs (darts_of E)` ⟹ every vertex of
   `E` has ≥ 2 incident undirected edges (≥ 2 outgoing darts at each `v` in
   `verts E`). Bridge `no_spurs` (a face-step / leaf statement) to a degree
   count via `outgoing` / `fan_ok`.
2. Lemma `verts_E_minus_eq_of_min_degree_2`: under min-degree-2, `verts
   (E_minus E e)` and `verts E` have the same `nodup` length — each endpoint
   of the removed `e` survives on another edge.
3. Conclude H7. Remove H7 from `extract_rings_valid`'s hypothesis list,
   discharging it internally from `no_spurs` (already present as H2).

This is the highest-value, lowest-risk rung: it strictly shrinks the carried
hypothesis set and reuses an already-supplied premise.

### H4 — `NoDup E` *(DONE — 2026-06-16)*

**Landed** with zero blast radius (route (a) — proved from the construction,
no definition changes). `result_edges op g = map fst (filter … (tg_edges g))`;
`tg_edges (noded_labeled_graph A B) = merge_labeled_edges …`, whose keys
(`edge_keys := map fst`) are `NoDup` by `OverlayGraph.merge_NoDup_keys`. New
helpers `ExtractFaces.NoDup_map_fst_filter` + `NoDup_result_edges_of_keys`
carry distinctness through the `map fst`/`filter`, and
`OverlayBridge.NoDup_result_edges_noded` instantiates it for the noded graph.
The three headlines drop the carried `NoDup` premise and derive it internally;
`H_bridge_premise_from_euler` keeps its own `NoDup E` parameter.

### H3 — `edge_2_connected E` *(IRREDUCIBLE; equivalence completed — 2026-06-16)*

**Finding:** `edge_2_connected` is **not** dischargeable from geometry. A planar
**dumbbell** (two cycles joined by a bridge) satisfies `valid_geometry` +
`well_noded_darts` + `no_spurs` yet has a cut edge. So, like the planar-Euler
instances (H5/H6), it is an irreducible topological precondition and stays
carried.

**What landed (the valuable contribution):** the rotation-system bridge
characterisation now has **both** directions in `theories/EdgeFaceBridge.v` §4b:
- FORWARD (pre-existing) `edge_2_connected_twins_sep` — `edge_2_connected ⟹
  twins_in_different_faces`, the genus-0 side, modulo the planar
  `H_bridge_premise`.
- CONVERSE (new) `twins_in_different_faces_edge_2_connected` — `≡` the easy
  different-faces ⟹ not-a-bridge side, **Euler-free** (`Print Assumptions`
  shows only the standard allowlist). Built from `diff_face_bypass_E_minus`
  (the rest of a dart's face walk is a bypass in `E_minus`) +
  `reachable_E_minus_implies_not_cut`, reusing `dart_on_walk_endpoints_adj_E_minus`.

**And** reduced-hypothesis headline variants in `theories-flocq/OverlayBridge.v`
§8b — `extract_rings_valid_sep`, `extract_rings_valid_holes_sep`,
`valid_geometry_extract_sep` — carry `twins_in_different_faces (result_darts …)`
directly, dropping `edge_2_connected` + both `euler_characteristic` instances +
`NoDup` (the Euler stack only served the forward direction). The original
Euler-routed headlines are kept unchanged.

### H5 / H6 — the planar Euler identity *(irreducible; route A confirmed; non-vacuity witness landed 2026-06-16)*

Goal: `euler_characteristic E` and `euler_characteristic (E_minus E e)` for
every `e`.

**Status:** confirmed irreducible and carried (route A). A **non-vacuity
witness** landed in `theories/EulerWitness.v` — `w1_euler :
euler_characteristic [(a,b)]` (the analogue of `single_edge_is_cut`), proving
the premise is correct and satisfiable on a concrete arrangement (V=2,F=1,E=1,
C=1) via the singleton-fan `fstep` reduction + `count_classes_eq_1`. The
`euler_characteristic` definition is **never proven in general** (16 sites, all
hypotheses) — confirmed greenfield. Two further witnesses are **deferred**
(documented in `EulerWitness.v` §3): W2 (two disjoint edges, would validate the
`2*C` coefficient with C=2 — blocked on `same_orbit_b` transitivity =
`fstep` injectivity case-work) and W3 (triangle, the canonical genus-0 face —
degree-2 fans need concrete angular `lra`).

This is a **genus-0** fact. As documented in `EdgeFaceBridge.v:1340`,
per-vertex `fan_ok` constrains only the *local* angular order at each vertex;
it does **not** pin the genus. A non-planar rotation system can satisfy every
local condition yet violate `V + F = E + 2·C`. So H5/H6 require a genuine
planarity input.

Two routes:

- **(A) Keep carried (recommended).** Continue to carry the planar Euler
  identity as a named `Prop` premise, discharged per-instance by the embedding.
  This matches the corpus convention for irreducibly-geometric inputs (cf.
  `parity_characterises_interior_cont`) and the explicit design note in
  `EulerArrangement.v:62`. The premise is never axiomatized — it is supplied at
  the call site from the concrete embedded arrangement.
- **(B) Prove genus-0 from geometry (large, multi-session).** Build the
  geometric→combinatorial planarity theorem: a rotation system induced by
  `outgoing v` over a set of pairwise-non-crossing planar segments
  (general position) embeds in the plane, hence is genus-0 and satisfies the
  Euler identity. This is a substantial new layer (planar embedding +
  Euler formula for plane graphs) with no current scaffolding.

Recommendation: **route (A).** The combinatorial reduction is complete; the
remaining geometric planarity is best carried as a named hypothesis supplied by
the embedding, exactly as `EulerArrangement.v` already frames it. Route (B) is
a worthwhile but independent long-horizon project and should not block
shrinking H4/H7 or landing H3.

## 4. Recommended ordering

1. ~~**H7** (vertex invariance from `no_spurs`)~~ — **DONE** (2026-06-16,
   `theories/VertexDegree.v`).
2. ~~**H4** (`NoDup E` from noding dedup)~~ — **DONE** (2026-06-16,
   `ExtractFaces.v` + `OverlayBridge.NoDup_result_edges_noded`).
3. ~~**H3** (`edge_2_connected`)~~ — **RESOLVED** (2026-06-16): irreducible
   (dumbbell), but the `twins_in_different_faces ⟺ edge_2_connected` equivalence
   is now proven both ways (converse is Euler-free), and `*_sep` headline
   variants carry the equivalent precondition directly.
4. ~~**H5/H6**~~ — **RESOLVED** (2026-06-16): irreducible (genus-0), carried by
   design (route A); non-vacuity witness `w1_euler` landed in
   `theories/EulerWitness.v`. Route B (prove genus-0 from geometry) is a
   separate greenfield planarity project.

## Seam analysis: COMPLETE (2026-06-16)

Every carried hypothesis of `extract_rings_valid` has been resolved — either
**discharged** or shown **irreducible** (and reduced to its honest form +
witnessed):

| # | Hypothesis | Outcome |
|---|-----------|---------|
| H1 | `well_noded_darts` | prerequisite (established) |
| H2 | `no_spurs` | prerequisite (established) |
| H7 | vertex invariance | **discharged** from `no_spurs` (`VertexDegree`) |
| H4 | `NoDup E` | **discharged** from the noding construction (`ExtractFaces`/`OverlayBridge`) |
| H3 | `edge_2_connected` | **irreducible** (dumbbell); ⟺ `twins_in_different_faces` proven both ways; `*_sep` variants carry the equivalent directly |
| H5/H6 | planar Euler identity | **irreducible** (genus-0); carried by design; witnessed by `w1_euler` |

The two genuinely irreducible geometric inputs are **(a)** 2-edge-connectivity
(`edge_2_connected` ⟺ `twins_in_different_faces`) and **(b)** the planar-Euler
identity. Both are now precisely characterized, honestly carried, and
non-vacuously witnessed. `face_twin_free` itself needed no direct work (§5).
Remaining greenfield project: route B (geometric→combinatorial planarity to
discharge H5/H6 unconditionally).

## 5. Note: `face_twin_free` needs no direct further work

`spur_breaks_face_twin_free` (`FaceTwinAware.v:371`) records that a spur step
breaks twin-freeness; the FaceTwinAware header's "deriving `face_twin_free`
from a no-spur condition is its own follow-up rung" was written before
`face_twin_free_of_sep` landed. That reduction now exists and is `Qed`, so the
per-face predicate is fully accounted for via the global
`twins_in_different_faces` route. No work remains on `face_twin_free` as such —
only on the hypotheses in §2.
