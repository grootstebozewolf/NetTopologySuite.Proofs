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
| H3 | `edge_2_connected E` | **carried** | **open** |
| H4 | `NoDup E` | **carried** | open (cheap) |
| H5 | `euler_characteristic E` | **carried** | **open (deep)** |
| H6 | `∀ e ∈ E, euler_characteristic (E_minus E e)` | **carried** | **open (deep)** |
| H7 | `∀ e ∈ E, num_vertices (E_minus E e) = num_vertices E` | **carried** | open (cheap) |

`euler_characteristic` is `num_vertices E + num_faces E = num_edges E + 2 *
num_components E` (`EulerArrangement.v:76`), the subtraction-free genus-0 Euler
relation for the combinatorial map (rotation system). The `2·C` (not `1+C`) is
deliberate: the bridge argument's `E_minus` side is *disconnected*, and the
identity must survive that.

## 3. Discharge plan, by hypothesis

### H7 — vertex invariance under edge deletion *(recommended first rung)*

Goal: `∀ e ∈ E, num_vertices (E_minus E e) = num_vertices E`.

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

### H4 — `NoDup E`

Goal: the noded survivor edge list has no duplicate undirected edge. This
should fall out of the noding step producing a de-duplicated survivor set
(`result_edges`). Plan: locate where `result_edges` is built in the noding
pipeline (`noded_labeled_graph` / `snap_noding`) and either (a) prove
`NoDup (result_edges …)` from a `nodup`/dedup in the construction, or (b) if
the construction does not dedup, insert a `nodup edge_eq_dec` normalisation
and re-prove the downstream `count_occ … = 1` uses (only `count_occ_1_of_NoDup`
in `HBridgeEuler.v` consumes it). Cheap, mechanical.

### H3 — `edge_2_connected E`

Goal: no edge of the noded arrangement is a cut edge.

Mathematical content: in the overlay of **closed area boundaries** (valid
`Geometry` rings), every edge bounds a 2-D face on each side, so every edge
lies on a boundary cycle ⟹ no bridges within a component. `no_spurs` already
removes the degree-1 antenna; H3 is exactly the complementary "no dumbbell
bridge" condition.

Plan:
1. Define / locate the structural fact "every edge of `E` lies on an
   `fstep`-face cycle of length ≥ 3" — this is essentially already available
   (`face_period ≥ 3` via `no_short_faces_of_proper_nospur`, and every dart is
   on its period walk).
2. Prove `on_two_face_cycles ⟹ ~ is_cut_edge`: an edge whose two darts lie on
   *distinct* faces has a bypass after removal (each face boundary minus the
   edge is a path between its endpoints). Note this is the **converse** side of
   `same_face_twin_is_cut`; the machinery (`dart_on_walk_endpoints_adj_E_minus`,
   `reachable_E_minus_implies_not_cut`) is already in `EdgeFaceBridge.v`.
3. Assemble `edge_2_connected E` for the noded overlay of valid area
   geometries, threading the "closed-boundary" hypothesis from the input
   `Geometry` validity.

Risk: medium. The honest precondition is that inputs are *area* geometries
whose overlay has no dangling edges; degenerate point/line contacts must be
handled (or excluded by the input contract). This is where to surface the
precondition explicitly rather than over-claim.

### H5 / H6 — the planar Euler identity *(deepest; recommend keeping carried)*

Goal: `euler_characteristic E` and `euler_characteristic (E_minus E e)` for
every `e`.

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

1. **H7** (vertex invariance from `no_spurs`) — removes a carried hypothesis,
   reuses H2, pure combinatorics. Do this first.
2. **H4** (`NoDup E` from noding dedup) — mechanical.
3. **H3** (`edge_2_connected` from closed-boundary overlay) — the substantive
   structural rung; reuses existing `EdgeFaceBridge` bypass machinery.
4. **H5/H6** — keep carried (route A); revisit route (B) only as a separate
   planarity project.

After steps 1–2, `extract_rings_valid` would carry only `well_noded_darts`,
`no_spurs`, `edge_2_connected`, and the two planar Euler instances — the
honest, irreducible geometric inputs.

## 5. Note: `face_twin_free` needs no direct further work

`spur_breaks_face_twin_free` (`FaceTwinAware.v:371`) records that a spur step
breaks twin-freeness; the FaceTwinAware header's "deriving `face_twin_free`
from a no-spur condition is its own follow-up rung" was written before
`face_twin_free_of_sep` landed. That reduction now exists and is `Qed`, so the
per-face predicate is fully accounted for via the global
`twins_in_different_faces` route. No work remains on `face_twin_free` as such —
only on the hypotheses in §2.
