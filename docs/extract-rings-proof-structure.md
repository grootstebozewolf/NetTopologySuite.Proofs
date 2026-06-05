# `extract_rings_valid` — proof structure & plan (hole-topology route)

> **Status: PLAN ONLY.** No Coq in this document; no proof attempted yet.
> This captures, while the buffer hole-formation work is fresh, a route to
> the registered deferred proof `extract_rings_valid`
> (`theories-flocq/OverlayBridge.v`, `docs/admitted-deferred-proofs.txt`)
> that leans on the corpus's existing **bounded-complement-component**
> machinery and the **hole-count heuristic** rather than on a full DCEL
> rebuild. It extends — does not replace — the DCEL plan in
> [`docs/audit-phase3-milestone5.md`](audit-phase3-milestone5.md) §4.3 / §5.2.

---

## §1 The obligation

```coq
(* theories-flocq/OverlayBridge.v — Admitted, registered deferred *)
Lemma extract_rings_valid :
  forall (op : BooleanOp) (A B : Geometry),
    valid_geometry A -> valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    forall poly, In poly (extract op (noded_labeled_graph A B)) ->
      valid_polygon poly.
```

`valid_polygon` (`theories/Overlay.v:268`) is the conjunction of four OGC
§6 conditions on the outer ring and every hole:

| condition | `Overlay.v` | character |
|---|---|---|
| `ring_closed` | 235 | **combinatorial** (first = last vertex) |
| `ring_has_minimum_points` | 262 | **combinatorial** (`4 <= length`) |
| `ring_simple` | 244 | **analytic** (no proper self-intersection in ℝ²) |
| `hole_inside_outer` | 256 | **analytic** (a hole vertex is `point_in_ring` the outer) |

The current `extract` (`theories/OverlayGraph.v:653`) is the naive
S2 form: `List.filter` the edges by `edge_in_result op`, then `flat_map`
the survivors' endpoints into **one** ring. It does *not* satisfy
`valid_polygon` in general (the flattened endpoint list is neither closed
nor simple, and collapses all faces into a single "ring").

## §2 Why this has been deferred

Two independently thesis-shaped sub-problems (audit-phase3-milestone5.md
§4.3, §5.2):

1. **Assembly.** Turn the unordered surviving-edge set into *ordered closed
   walks* = the face boundaries of the planar subdivision. The standard
   tools (DCEL traversal, or cyclic-order-around-vertex Euler walks) are
   not in the stdlib, and `TopologyGraph` stores edges unordered with no
   face/incidence data. The recorded estimate is a 5–7 session DCEL rebuild.
2. **Geometric validity.** `ring_simple` and `hole_inside_outer` are
   point-set / Jordan-curve facts, entangled with the absent JCT toolkit
   (the same gap as H1 in `overlay_ng_correct_conditional`).

## §3 The lever: the hole-formation / dissolving heuristic

[`oracle/buffer_hole_count.py`](../oracle/buffer_hole_count.py) computes
the hole count of a region by **rasterising it on a grid, flood-filling the
complement, and counting bounded components** (components that do not touch
the grid border). Its self-test encodes the non-monotonic C-shape law:

```
  d:   0.0  0.3  1.0  2.0  3.0  5.0  8.0
holes:  0    0    1    1    0    0    0     (mouth seals -> hole; pocket fills -> gone)
```

i.e. a hole **forms** when a concavity's mouth seals and **dissolves** when
the pocket fills — `0 → 1 → 0`.

The decisive observation for this plan: **"bounded component of the
complement" is already a corpus predicate.**
`theories/PointInRingTangents.v` ships

```coq
ring_complement r q        := ~ ring_image r q          (* off the edge skeleton *)
connected_in_complement r p q := exists path, ... stays in ring_complement
in_bounded_component r p   := exists M>0, reachable q stay within radius M
geometric_interior_stdlib p r := ring_complement r p /\ in_bounded_component r p
```

`buffer_hole_count` is the **computable, grid-discretised oracle for
`in_bounded_component`**: each bounded flood-fill component is a witness
that its points are `in_bounded_component`, and "touches the border" is the
refutation (an unbounded path to infinity). So the heuristic is not a proof
device by itself, but it (a) gives a RocqRefRunner-style **differential
oracle** for any executable ring/face extractor, and (b) tells us the right
**invariant** to prove: *the assembled bounded faces are in bijection with
the heuristic's bounded complement components.*

## §4 Reframing `valid_polygon`: combinatorial core vs analytic shell

Split the obligation along the table in §1.

- **Combinatorial core (target of this plan, tractable):** `ring_closed`
  and `ring_has_minimum_points` hold *by construction* of a face walk, and
  hole nesting can be stated **combinatorially** as a parity/winding
  relation on faces rather than as point-set containment.
- **Analytic shell (kept deferred / named):** the upgrade of combinatorial
  nesting to the point-set `hole_inside_outer`. Remains JCT-adjacent.

The win: discharge the core unconditionally, and shrink the residual to a
*single* analytic hypothesis (the combinatorial→point-set nesting bridge)
that is strictly smaller than today's whole-of-`valid_polygon` gap — and
that the heuristic validates empirically.

> **`ring_simple` resolved (`theories/RingSimple.v`).** Contrary to the
> first cut above, `ring_simple` is **not** the hard analytic residual — it
> is **delivered by the noder**: `ring_simple_of_subset` proves a ring whose
> edges are drawn from a pairwise-non-properly-crossing (i.e. NODED)
> arrangement is `ring_simple` (instantiate with the snap-rounding noder's
> `fully_intersected` output). The *raw* offset is genuinely not simple
> (`not_ring_simple_bowtie`, a verified self-crossing counterexample — the
> hole-forming sealing mouth), which is precisely why the pipeline nodes
> before extracting. So the only remaining analytic residual is
> `hole_inside_outer`'s point-set half (= the H1/JCT gap of R3).

## §5 Proposed structure — half-edge faces + bounded-component invariant

A "DCEL-lite" that avoids re-doing M2's lemmas: keep `TopologyGraph` as is,
and define face walks as a *derived* notion.

1. **Half-edges.** For the surviving edge multiset, form directed
   half-edges (each undirected edge → two darts). `next` around a vertex =
   the cyclic successor by angle (`Azimuth.turn_sign` gives the comparison;
   no atan needed for a cyclic order via half-plane + cross-product sign).
2. **Face walk.** `face_of dart` = iterate `next ∘ twin`; a face is the
   orbit. **Targets (combinatorial, by induction on the orbit):**
   - `face_walk_closed`: every face orbit is a `ring_closed` ring.
   - `face_walk_min_points`: a bounded face orbit has `>= 4` vertices
     (a face of the fully-noded arrangement has no spurs).
3. **Bounded-face ↔ component invariant.** Prove the orbit-count /
   Euler relation `V - E + F = 1 + C` (C = connected components) so that
   **#bounded faces is determined combinatorially**, and connect a bounded
   face's interior points to `in_bounded_component` of its boundary ring.
   - `bounded_face_in_bounded_component`: a point strictly inside a bounded
     face orbit satisfies `in_bounded_component (face_ring) p`.
   This is the rung that the heuristic's flood-fill *counts*; the proof is
   a discrete reachability argument (no analytic JCT), mirroring the
   parity machinery already in `Overlay.ray_parity_odd` /
   `Overlay.point_in_ring`.
4. **`extract` re-defined** to emit `{ outer_ring := bounded-face-walk ;
   hole_rings := nested inner face-walks }`, with hole nesting read off the
   face-incidence tree (step 3), then `extract_rings_valid` becomes:
   composition of `face_walk_closed` + `face_walk_min_points` (core, Qed) +
   the residual analytic `ring_simple`/nesting bridge (named).

## §6 The tractable beachhead: specialise to **buffer**

The general overlay arrangement is arbitrary; the **buffer** offset curve
is not. For the buffer pipeline (`theories/BufferCorrectness.v`), the
output's hole topology is exactly the C-shape law the heuristic verifies:
holes are the pockets that *sealed but did not fill*. This is far more
structured than a generic two-geometry overlay.

**Proposal:** prove a buffer-specialised `extract_buffer_rings_valid`
first — it discharges the `H_valid` hypothesis of
`buffer_correct_conditional` for the buffer pipeline — using:
- the offset/join/cap geometry already Qed-closed
  (`BufferOffset`, `BufferJoin`, `BufferMiter`, `BufferBevel`,
  `BufferEndcap`): the raw curve's local structure is known exactly;
- the heuristic's hole law as the *specification* of which bounded faces
  survive (mouth-sealed-not-filled ⇒ hole), differentially tested;
- the §5 face machinery, but over the buffer curve's restricted topology
  (single input ring ⇒ at most the pockets as holes), where `ring_simple`
  of the offset is controlled by the parallel/limit results we already have
  (`offset_seg_parallel`, `miter_within_limit_iff`).

Closing the buffer case unblocks a real consumer (issue #65 / JTS#979)
without waiting on the fully-general DCEL + JCT.

## §7 Slice plan

| # | Slice | Ends in | Risk |
|---|---|---|---|
| R1 | Half-edge / dart layer + cyclic `next` via `turn_sign`; `face_of` orbit definition. | **✅ refined + LANDED** `theories/RingExtract.v` | low |
| R2 | `face_walk_closed`, `face_walk_min_points` (combinatorial, by orbit induction). | **✅ LANDED (Qed, axiom-free)** | low-med |

> **R1+R2 landed (`theories/RingExtract.v`, axiom-free).** Refinement: a
> *face walk is a closed chain of edges*, and `BufferAssembly` already
> produces such chains as concrete finite lists — so we take the face walk
> as a `closed_chain` (finite by construction, sidestepping the
> `face_orbit_finite` crux of §9) and extract its ring directly.
> `ring_of_chain` maps a chain to a `Ring`; `face_walk_closed` gives
> `ring_closed`; `face_walk_min_points` gives `ring_has_minimum_points` for
> ≥3 segments; `ring_edges_of_closed_chain` proves the ring's edges are
> **exactly** the chain (the faithful assembly↔ring bridge); `face_walk_core`
> bundles the three. This is the §6 buffer beachhead's combinatorial core.
> **Still open in R1:** ordering an *unordered* overlay edge set into chains
> (the dart/`next`/`turn_sign` assembly) — needed for the general (non-buffer)
> case. **Still the analytic shell (§4):** `ring_simple`, `hole_inside_outer`.
| R3 | `bounded_face_in_bounded_component` — discrete reachability ↔ `PointInRingTangents.in_bounded_component`. | **🟡 structure LANDED (Qed); geometric rung = named residual** `theories/BoundedComponent.v` | **med** (the heuristic's invariant) |

> **R3 split landed (`theories/BoundedComponent.v`, JCT-free).** The
> *component structure* the heuristic counts is now rigorous:
> `connected_in_complement` is an equivalence relation on the complement
> (`_refl`/`_sym`/`_trans`, via explicit reparametrisations — the path
> relation carries no continuity obligation, so this needs no analysis);
> `in_bounded_component` is a **component invariant** (`in_bounded_component_iff`
> — boundedness is constant on a connectivity class); and
> `not_in_bounded_component_intro` refutes boundedness from unbounded
> reachability (the tool for the OUTER face). So "bounded component" is a
> well-defined notion = what `buffer_hole_count.py` flood-fills.
> **The geometric rung stays the named residual:** that a point strictly
> inside an assembled face lies in a *bounded* class (the ring separates the
> plane into bounded inside / unbounded outside) is the Jordan-curve content
> — identical to `overlay_ng_correct_conditional`'s H1 / `point_in_ring` ↔
> `geometric_interior_stdlib`. It is carried as a downstream hypothesis (R6),
> **not admitted** (no new registry debt).
| R4 | Euler / face-count `V-E+F` relation; #bounded faces = heuristic component count (oracle bridge). | Qed + differential test | med |
| R5 | Re-define `extract` (or `extract_buffer`) to emit face-walk rings + nesting tree. | defs | low |
| R6 | `extract_buffer_rings_valid` = R2 ⊕ `ring_simple`; discharge `BufferCorrectness.H_valid`. | **✅ LANDED (Qed), hole-free unconditional** `theories/ExtractBufferRings.v` | med |

> **R6 landed (`theories/ExtractBufferRings.v`).** For the **hole-free**
> regime, `valid_polygon` is just its three outer-ring conditions, all now
> Qed: `valid_polygon_of_noded_chain` proves a hole-free polygon whose outer
> ring is a closed chain (≥3 segs) from a noded set is `valid_polygon`,
> **with NO Jordan-curve residual** (composes R2 `face_walk_core` + RingSimple
> `ring_simple_of_subset`). `H_valid_of_chain_extractor` lifts this to
> `BufferCorrectness`'s `H_valid` for any extractor meeting `chain_extractor_spec`,
> and `buffer_correct_hole_free` plugs it into `buffer_correct_conditional` —
> so for hole-free buffers the headline reduces to **just the semantic
> `H_bridge`**. The with-holes path (`valid_polygon_with_holes`) carries the
> `hole_inside_outer` clause as the single H1/JCT hypothesis (R3's residual).
| R7 | (stretch) general `extract_rings_valid`; or register the residual analytic shell as a *smaller* deferred entry. | **✅ analytic shell COMPLETED (Qed)** `theories/ExtractRingsShell.v` | high |

> **R7 analytic shell landed (`theories/ExtractRingsShell.v`).** The
> with-holes case no longer carries the whole per-hole conjunction as an
> opaque hypothesis. `hole_noded_chain_conditions` discharges a hole's
> `ring_closed` + `ring_simple` + `ring_has_minimum_points` from its being a
> noded closed chain (the same combinatorial + `ring_simple_of_subset` route
> as the outer ring), so `valid_polygon_noded_shell` reduces `valid_polygon`
> (outer + holes) to EXACTLY ONE analytic clause: the per-hole
> `hole_inside_outer` nesting. `H_valid_of_chain_extractor_holes` /
> `buffer_correct_with_holes` lift this to `BufferCorrectness.H_valid` and the
> end-to-end headline for the with-holes regime, modulo only that single
> JCT/nesting seam (R3's residual = H1 of `overlay_ng_correct_conditional`).
> The combinatorial core + `ring_simple` of the analytic shell are now Qed for
> outer rings AND holes alike; the only thing left of `extract_rings_valid`'s
> geometry is the point-set nesting bridge.

Each slice is independently `Qed`-able or ends in a documented, **smaller**
registered sub-deferred entry — never a silent stub. The combinatorial
core (R1–R2, R5) carries no analytic content and should close cleanly;
R3–R4 are where the heuristic earns its keep; R6 is the headline beachhead.

## §8 Oracle bridge (differential testing)

Extract the executable face/ring assembler (Coq → OCaml, RocqRefRunner
pattern) and test bounded-face counts against
`oracle/buffer_hole_count.py` on the C-shape family and the JTS#979
fixed-precision cases. Mismatch = a bug in the assembler *or* a too-coarse
grid (`res`); convergence under refinement is the acceptance gate. This
gives confidence in R5's definition *before* R6's proof, exactly as the
orientation / intersection lanes were de-risked.

## §9 Risks & decision points

- **Cyclic order without atan.** `next`-around-vertex needs a total cyclic
  order of darts. Use the half-plane split + `turn_sign` (cross-product
  sign) comparator — stays 3-axiom; avoid `Azimuth`/`atan2` to keep the
  combinatorial layer classic-clean. *Decision at R1.*
- **R3 is the crux.** If the discrete reachability ↔ `in_bounded_component`
  bridge resists (it is a small Jordan-flavoured argument), fall back to
  carrying it as the *named residual hypothesis* of R6 — still a strict
  shrink of today's gap, and the heuristic certifies it case-by-case.
- **`ring_simple` — RESOLVED (was thought analytic).** It is delivered by
  the noder, not by ℝ²-geometry: `RingSimple.ring_simple_of_subset` derives
  it from the noded arrangement's pairwise-non-crossing property
  (`fully_intersected`), and `not_ring_simple_bowtie` shows the raw offset
  is not simple (hence noding is required). No longer a residual.
- **Scope discipline.** Anything not `Qed` at the end of a slice is added
  to `docs/admitted-deferred-proofs.txt` as a *narrower* entry than
  `extract_rings_valid`, with its own section here.

## §10 References

- Obligation: `theories-flocq/OverlayBridge.v:extract_rings_valid`;
  `docs/admitted-deferred-proofs.txt`; `docs/audit-phase3-milestone5.md`
  §4.3, §5.2, §5.3.
- Reused predicates: `theories/PointInRingTangents.v`
  (`ring_complement`, `connected_in_complement`, `in_bounded_component`,
  `geometric_interior_stdlib`); `theories/Overlay.v`
  (`ring_edges`, `ray_parity_odd`, `point_in_ring`, `valid_polygon`,
  `ring_*`); `theories/OverlayGraph.v` (`extract`, `build_graph`);
  `theories/Azimuth.v` (`turn_sign`).
- Heuristic / oracle: [`oracle/buffer_hole_count.py`](../oracle/buffer_hole_count.py)
  (JTS#979 family).
- Consumer: `theories/BufferCorrectness.v:buffer_correct_conditional`
  (the `H_valid` hypothesis this would discharge for the buffer pipeline);
  buffer geometry `theories/Buffer{Offset,Join,Miter,Bevel,Endcap}.v`.

## §11 2026-06-05: status — combinatorial core complete; frontier = the JCT residual

A re-audit of this lane (R1–R7 all landed on `main`) shows the slice plan is,
for practical purposes, **mined out down to a single analytic obstruction**.
What is Qed-closed and what remains:

**Qed-closed (combinatorial + noder-delivered `ring_simple`), JCT-free:**
- R1+R2 face-walk core — `theories/RingExtract.v` (`ring_of_chain`,
  `face_walk_closed`, `face_walk_min_points`, `ring_edges_of_closed_chain`,
  `face_walk_core`).
- R3 *component structure* — `theories/BoundedComponent.v`
  (`connected_in_complement` equivalence; `in_bounded_component` invariant;
  `not_in_bounded_component_intro`).
- `ring_simple` — RESOLVED via the noder (`RingSimple.ring_simple_of_subset`
  + `not_ring_simple_bowtie`); not an analytic residual.
- R6 hole-free `valid_polygon` + `H_valid` + end-to-end
  `buffer_correct_hole_free` / `buffer_correct_hole_free_split` —
  `theories/ExtractBufferRings.v`, `theories/BufferBridge.v`. **No JCT.**
- R7 analytic shell — `theories/ExtractRingsShell.v`
  (`hole_noded_chain_conditions`, `valid_polygon_noded_shell`,
  `H_valid_of_chain_extractor_holes`, `buffer_correct_with_holes`): the
  with-holes case is reduced to EXACTLY ONE analytic clause.

**The single remaining residual (thesis-scale, JCT-gated):** the point-set
`hole_inside_outer` nesting bridge = R3's geometric rung = "a point strictly
inside a bounded face orbit lies in `in_bounded_component` of its boundary
ring". This is **the same theorem** as:
- `overlay_ng_correct_conditional`'s H1 (`OverlayCorrectness.v`);
- `parity_characterises_interior_cont` (`theories/JCT.v:398`);
- the `point_in_ring` ↔ `geometric_interior_cont` equivalence.

**Strategic consequence.** All of the corpus's remaining *general* headlines —
general `extract_rings_valid`, with-holes buffer, OverlayNG correctness —
**converge on this one polygonal-Jordan-Curve fact.** The hole-free buffer
headline is already unconditional. The combinatorial assembly that is still
JCT-free but unlanded is narrow:
- **R1-open:** ordering an *unordered* overlay edge set into closed chains
  (the dart / `next`-via-`turn_sign` machinery; `face_orbit_finite` is the §9
  crux). Needed only for the *general* (non-buffer) case.
- **R4:** the Euler `V − E + F = 1 + C` face-count relation (oracle bridge).

**Cost/risk update.** The recorded "5–7 session DCEL" estimate is largely
*spent*: the combinatorial core landed and the hole-free buffer consumer is
discharged. Remaining headline value in this lane is **JCT-gated** (the same
3–5-month topology piece tracked for #65), with R1-open / R4 as the only
incremental, JCT-free combinatorial work left — valuable for the general case
but not reaching a headline on their own.
