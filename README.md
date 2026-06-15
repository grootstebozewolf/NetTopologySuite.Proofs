# NetTopologySuite.Proofs

[![build proofs](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/actions/workflows/ci.yml/badge.svg)](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/actions/workflows/ci.yml)

Mechanically-verified formal proofs of foundational properties of the
geometry algorithms in
[NetTopologySuite](https://github.com/NetTopologySuite/NetTopologySuite),
written in [Rocq Prover](https://rocq-prover.org/) (formerly Coq).

> **New here?**  
> Run `make help` (works with no Rocq installed) or open  
> [`docs/HELP.md`](docs/HELP.md) — the friendly "pick your path" card deck.  
> Full role navigation lives in [`docs/READING-GUIDE.md`](docs/READING-GUIDE.md).  
> `GETTING-STARTED.md` has the 60-second on-ramp.  
> **Never seen a proof assistant?** Start with the heavily commented
> [`docs/pythagoras-for-beginners.v`](docs/pythagoras-for-beginners.v)
> (step through it in an IDE). It also explains why even "obvious"
> theorems take serious machine time once everything must be checked.
>
> A second beginner-friendly example is
> [`docs/sqrt3-irrational-for-beginners.v`](docs/sqrt3-irrational-for-beginners.v),
> which proves the classic fact that `sqrt 3` is irrational by infinite
> descent (with a detailed honesty note about what the proof does *not*
> say regarding tilings or the Spectre monotile).

---

**Over 1,100 theorems — every proof sealed with `Qed.`** (or `Defined.`
for computable terms), **resting on three axioms.** Those three are the
standard classical-reals trio Rocq ships with; this corpus introduces
none of its own, and `Axiom`, `Parameter`, and the `admit.` tactic are
banned outright and appear nowhere. The *only* proofs not closed by
`Qed.` are **6** `Admitted` theorems — and an unregistered `Admitted`
fails the build, so there is no quiet middle ground. All six fall into
a single honest category, each with a concrete seam on file: **6
counterexamples** (the theorem as stated is *false*, with a verified
counterexample committed). The deferred-proof registry is now **empty
(0)** — its sole former entry, `EdgeFaceBridge.H_bridge_core`, has been
discharged via the planar Euler route, leaving only named planar Euler
hypotheses on the headline `extract_rings_valid` (a conditional Qed).
No soundness bridge is silently stubbed — each is proven, absent, or
registered. (The Flocq-dependent lane inherits one further axiom
structurally from Flocq's binary64 model — not load-bearing, and
detailed below.)

CI (`scripts/check_admitted.sh`) enforces a three-tier `Admitted`
discipline across both directories:

- **Tier 1** — an `Admitted` with no registry entry is a build failure.
  This is the default.
- **Tier 2** — an `Admitted` registered in
  [`docs/admitted-counterexamples.txt`](docs/admitted-counterexamples.txt)
  is allowed permanently: the theorem *as stated* is false, with a
  verified counterexample on file. 6 entries today: three in the Stage D
  expansion-arithmetic work (`b64_grow_expansion_nonoverlap` and two
  companions), Hobby Lemma 4.3's no-proper-intersection half
  (`hobby_lemma_4_3_no_proper`) — false for arbitrary, non-noded segment
  pairs (`HobbyCounterexample_b64.v`), Shewchuk Theorem 13's general
  headline (`fast_expansion_sum_nonoverlap_shewchuk`) and O7 completeness
  (`cascade_pathAB_chain_from_nonoverlap`) — both **false as stated**
  because half-ulp `strict_succ_b64` is stronger than Shewchuk's bit-disjoint
  nonoverlapping ([`B64_Shewchuk_Thm13_counterexample.v`](theories-flocq/B64_Shewchuk_Thm13_counterexample.v),
  [`docs/shewchuk-thm13-headline-counterexample.md`](docs/shewchuk-thm13-headline-counterexample.md)).
- **Tier 3** — an `Admitted` registered in
  [`docs/admitted-deferred-proofs.txt`](docs/admitted-deferred-proofs.txt)
  is allowed temporarily: the theorem is *true*, its proof structure is
  documented, and the remaining work is multi-session. **0 entries today —
  the registry is empty.** Its sole former entry,
  `EdgeFaceBridge.H_bridge_core` (the planar same-face⇒bridge seam behind
  Phase 3's ring assembly), has been discharged via the planar Euler route:
  the bridge fact is now a named premise threaded through the EdgeFaceBridge
  chain and proved in `theories/HBridgeEuler.v` from the named planar Euler
  identity, so `extract_rings_valid` carries those Euler hypotheses as a
  conditional Qed with no `Admitted`. An entry comes off the registry only
  when the proof lands. (Hobby Lemma 4.3's no-proper-intersection half,
  Shewchuk Theorem 13's headline, and O7 completeness were previously here;
  each is now a Tier-2 counterexample — machine-checked **false** as stated.)

The only axioms used are the three standard ones bundled with Rocq's
classical real arithmetic library (printed at the end of each `theories/`
`.v` file under `Print Assumptions` for transparency):

```
ClassicalDedekindReals.sig_not_dec
ClassicalDedekindReals.sig_forall_dec
FunctionalExtensionality.functional_extensionality_dep
```

A per-theorem axiom audit (`scripts/audit_axioms.sh`, run in CI against
per-file output-synced build chunks covering the whole corpus on every
run) checks every `Print Assumptions` block
against [`docs/axiom-allowlist.txt`](docs/axiom-allowlist.txt), and
[`scripts/check_readme_axioms.sh`](scripts/check_readme_axioms.sh)
guarantees the list above never drifts from that allowlist. The whole of
`theories/` is clean against this three-axiom set. `theories-flocq/`
*additionally* inherits a fourth axiom, `Classical_Prop.classic`,
transitively from Flocq's binary-arithmetic operations (`Binary.Bplus` /
`Bminus` / `Bmult` carry it in their definition closure) — a structural
consequence of using Flocq as the binary64 model, not a load-bearing
axiom this corpus introduces. The affected files are enumerated with
per-file rationale in
[`docs/audit-exceptions.txt`](docs/audit-exceptions.txt), and the policy
trade-offs are analysed in
[`docs/category-c-policy.md`](docs/category-c-policy.md). No
corpus-specific or load-bearing axiom is introduced anywhere.

The repository has two source directories:

- **`theories/`** — Stdlib-only modules. Builds on the host runner
  (macOS-latest with Homebrew Rocq); this is the CI canonical target.
- **`theories-flocq/`** — modules that additionally depend on Flocq,
  plus the Stdlib-only Phase 3/4 modules built alongside them. Builds
  inside the container only (host CI runner has no Flocq). The
  registry-tracked `Admitted` discipline above applies HERE TOO — the
  directory split is about which CI runner builds the file (host vs
  container), not about which proof standard it meets.

The host `_CoqProject` builds the 25 foundational `theories/` modules;
the container `_CoqProject.full` builds the entire corpus (all 62
modules — 36 in `theories/`, 26 in `theories-flocq/`).

**Status.** The foundational layer (real-number, vector, distance,
orientation, segment, bbox, triangle, convex, lex-order, plus their
companions) is Qed-closed.  The curve-linearisation stack
(`Linearise` → `Simplify` → `Tin` → `Validate` → `Validate_decidable`)
is Qed-closed in the abstract, and its binary64 instance
(`Validate_binary64.v` + RocqRefRunner) ships to
[NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve).
The Phase 0–7 chokepoint sequence has advanced well into its early
phases: **Phase 0** (robust orientation) ships the Shewchuk Stage A
filter with integer-regime soundness **plus an exact full-`binary64`
orientation predicate proven sound over the entire double-coordinate
plane** (`Orient_b64_exact_full.v` — `b64_orient2d_exact_sound`, at three
axioms, no `Classical_Prop.classic`), with Stage D adaptive-filter
arithmetic still under way; **Phase 1** (robust segment intersection) is shipped
end-to-end (predicate + intersection-point forward-error bound + C#
port); **Phase 2** (snap rounding) has hot-pixel foundations, the
snap-rounding correctness invariant, a topological-correctness theorem
at the level the infrastructure supports, and Hobby Theorem 4.1 stated
as a Qed-closed conditional; **Phase 3** (planar overlay) reaches a
Qed-closed conditional headline (`overlay_ng_correct_conditional`); and
**Phase 4** (native curves) reaches its own Qed-closed conditional
headline via the Option-B chord-approximation route
(`arc_overlay_correct_chord_approx`). The remaining gaps in Phases 2–4
are carried as explicit named hypotheses or registered deferred proofs,
not silent stubs.

## Why this exists

Computational-geometry algorithms have subtle robustness properties — the
kind of bug you find three years later when an unusual coordinate
configuration trips a sign flip.  Unit tests sample behaviour at finitely
many points; formal proofs cover all of ℝ² simultaneously.

The intent is not to verify every line of NetTopologySuite — that's
infeasible.  Most of the C# code is plumbing.  The intent is to verify
the load-bearing primitives: the handful of small algorithms that, if
wrong, make everything above them suspect.  Orientation, distance, the
convex-hull invariants, the buffer-curve angle relations.

## Core primitives

Foundational geometry modules (Stdlib-only). These are the algebraic and
structural facts that the rest of the corpus cites.

**For most actors the detailed per-lemma lists below are not the best entry point.**
See the **Reading Guide** (`docs/READING-GUIDE.md`) or your role card in `HELP.md`
for the phase completion, audit, and proof-structure documents that are written
for your needs (GIS Gus, BIM Bea, Scholar Sam, Newbie Nate, etc.).

Key modules at a high level:
- `Distance.v`, `Orientation.v`, `Segment.v`, `Intersect.v` (soundness),
  `Vec.v`, `Bbox.v`, `Triangle.v`, `Convex.v`, `LexOrder.v` (and companions).

The individual theorems and proofs are in the `.v` files and are cited from the
phase documents. The long bullet lists that used to live here have been
condensed to keep the README scannable.
## In-flight work

**Modules atop the core primitives in active development.**

The detailed per-module catalogue that used to live here has been slimmed (see the actor Reading Guide for the right phase docs). High-level threads:

- The **curve-linearisation stack** (Linearise → Simplify → Tin → Validate + binary64 instance in theories-flocq), tracking the SQL/MM Spatial (ISO/IEC 13249-3) curve prototype.
- The **Phase 0–7 chokepoint** (robust orientation via Shewchuk, intersection, snap-rounding/Hobby, OverlayNG, native curves via chord-approx Option B). Stage D expansion arithmetic is current Phase 0 frontier.
- The **JCT seam** (`point_in_ring`/OverlayNG H1): the prior interior predicate is refuted vacuous, and the continuous-component spine (`JCT.v`) discharges the equivalence-relation + bounded-component-invariance algebra — so "the interior is trapped" (`no_path_from_interior_to_exterior`) is now a free corollary, isolating the genuine remaining work to a single named hypothesis `parity_characterises_interior_cont` (ray-parity ↔ continuous interior). A scope finding (`JCT_Counterexample.v`) shows `ring_simple` alone is too weak — the self-touching figure-8 bowtie passes all three structural premises yet has three complement components — and supplies the minimal fix `JCT_two_components_cont_simple` (adds vertex-distinctness `NoDup (removelast r)`). A second scope finding (`JCT_VertexGrazingCounterexample.v`) shows the parity seam's `no_horizontal_edge_at` guard is likewise too weak — a convex diamond's centre passes all four guards yet its rightward ray grazes a vertex, flipping parity — fixed by the generic-position guard `ray_avoids_vertices` (`parity_characterises_interior_cont_strict`); a third (`JCT_HorizontalEdgeCounterexample.v`) shows `no_horizontal_edge_at` is in turn *necessary*. The guard predicates now live upstream (`ring_vertices_distinct` in `Overlay.v`, `ray_avoids_vertices` in `PointInRingCorrect.v`) and **both headlines are re-pointed onto the strengthened seams** — `jct_cont_interior_is_geometric` onto `JCT_two_components_cont_simple`, `point_in_ring_correct_jct_cont` onto `parity_characterises_interior_cont_strict`. See [`docs/jct-proof-structure.md`](docs/jct-proof-structure.md), [`docs/jct-bowtie-counterexample.md`](docs/jct-bowtie-counterexample.md), [`docs/jct-vertex-grazing-counterexample.md`](docs/jct-vertex-grazing-counterexample.md), [`docs/jct-horizontal-edge-counterexample.md`](docs/jct-horizontal-edge-counterexample.md). A **special-case discharge** lands for **axis-aligned rectangles** (`RectangleJCT.v`): `point_in_ring_rect_iff` proves ray-parity ↔ the box by finite evaluation over the four edges (the grazing caveat does not bite — a strict-interior height coincides with no vertex), and the separation is then proved **unconditionally** for strict-interior points (`RectangleSeparation.v : rect_parity_characterises_interior`) — `point_in_ring p ↔ geometric_interior_cont p` with *no* residual hypothesis, via a 1-D IVT on the scalar field `box_min` (>0 inside, =0 on the edge skeleton, <0 outside), so a complement path can never change sign; the same JCT residual still blocks the general `extract_rings_valid` lane (`docs/extract-rings-proof-structure.md` §11). The IVT separation is abstracted into a reusable engine (`SeparationField.separation_via_field`) and a **second unconditional instance** lands for the **axis-aligned right triangle** — the first family with a *sloped* edge (`RightTriangleJCT.v` + `RightTriangleSeparation.v`: `right_triangle_parity_characterises_interior`), with the hypotenuse handled affinely via `s_hyp`, showing the recipe is not tied to axis-aligned edges. The separation field itself is generalised in `ConvexField.v` to `conv_min` (the `Rmin` over a list of half-plane inward slacks) with `convex_separation` wrapping the IVT engine, so an arbitrary convex polygon's bounded-component obligation reduces to supplying its edge half-planes plus a zero-set-on-skeleton and boundedness fact (`box_min`/`tri_min` are the rectangle/triangle instances). The **separation half generalises to an arbitrary CCW triangle** (`GeneralTriangleSeparation.v`, via the barycentric `ring` identities), and the **parity half** is reduced to a single named hypothesis `gtri_parity_spec` (`GeneralTriangleParity.v`, with `edge_cross_sign` bridging `edge_crosses_ray` to signed areas, and a RED non-vacuity check that the engine's interior predicate is genuinely inhabited). That parity half is then **discharged** (`GeneralTriangleJCT.v : general_triangle_parity_characterises_interior`), and the seam is carried to the **corrected off-ring form** `parity_characterises_interior_cont_offring` (covering exterior as well as interior points, off the skeleton; the on-edge counterexample `JCT_OnEdgeCounterexample.v` shows the bare strict form is too strong on the boundary). This off-ring seam is now **total** (unconditional) for a growing **family ladder** — rectangle (`RectangleOffringSeam.v`), general triangle (`GeneralTriangleOffringSeam.v`), right triangle (`ConvexOffringSeam.v`), and now the **diamond** (`DiamondOffringSeam.v : diamond_parity_seam_offring`), the **first convex four-gon** and the **first instantiation of the generic convex assembly** `ConvexOffringSeam.convex_parity_seam_offring_of`: the diamond is presented by its four edge half-planes and its two guarded-parity obligations are discharged via the already-Qed monotone-chain split (`MonotoneChainParity.bimonotone_split_parity`). The **bimonotone split itself is now constructed generically** (`MonotoneChainConstruction.v : bimonotone_split_unimodal`): from a purely combinatorial y-unimodality hypothesis on the vertex list — heights rise strictly to a single apex then fall strictly — the edges split into the skeletons of the rising prefix and falling suffix, with no use of convexity, reducing the split obligation to an arithmetic `cbn`/`lra` check (it re-derives the diamond split in one `apply`, and `hexagon_bimonotone` scales it to a genuinely convex hexagon, *n* = 6). The `interior_hits_one_chain` residual is now **closed** (`MonotoneChainCoverage.v : interior_hits_one_chain_of_edge_hps`, rung 4): the key algebraic identity `hp_slack (edge_inward_hp e) q = (wx-vx)*(py q-vy)-(wy-vy)*(px q-vx)` bridges `ConvexField.hp_slack` to `GeneralTriangleParity.edge_cross_sign`, so for an inc edge hp_slack > 0 means the ray IS crossed and for a dec edge it means NOT crossed; combined with a height-band coverage lemma (`chain_increasing_straddles_y`) and vertex-avoidance derived from `ray_avoids_vertices`, a strictly-interior point (`conv_min hps q > 0`) crosses exactly the increasing chain and misses the decreasing chain for any polygon family whose CCW inward half-planes are supplied in `hps`. Validated concretely on the diamond (4-gon) and hexagon (6-gon). The convex **hexagon** then lands as the **fifth total off-ring family** (`HexagonOffringSeam.v : hexagon_parity_seam_offring`) and the **first convex polygon with more than four edges** (*n* = 6): the interior-odd obligation is now a near one-liner via rung 4 (`hexagon_interior_chain_hit` + `bimonotone_split_parity`), and exterior-even is discharged by a six-edge per-band case analysis (each crossed chain edge fixes the straddling opposite edge by y-band; either all six slacks are nonnegative — contradicting `conv_min < 0` — or the two opposite straddling slacks are geometrically incompatible, with the four span-interior vertex heights excluded by `ray_avoids_vertices`). A general convex *n*-gon now remains open only on the convexity ⟹ y-unimodal vertex-order implication that feeds the split, plus a *general* (rather than per-family) exterior-even. The **y-modulator** (`ConvexYUnimodal.v`) opens the former: `hp_slack (edge_inward_hp (a,b)) c = cross a b c` exactly, so the half-plane convexity hypothesis `vertices_in_halfplane` *is* the all-CCW-left-turns orientation form (`convex_left_turns` — a GLOBAL condition that rules out the pentagram, whose local turns are all left), it names the `y_unimodal_decomposition` target and wires it to `bimonotone_split` (`y_unimodal_bimonotone`), supplies the max/min-height vertex locators, and validates on the diamond and hexagon; the residual narrows to the implication *convexity ⟹ y-unimodal decomposition* under a no-adjacent-tie general-position guard. As a showcase that the machinery holds famous shapes, the **hat** aperiodic monotile is a concrete non-convex 13-gon `Ring` (`HatMonotile.v`) — mechanized as closed, simple (`HatValidPolygon.hat_ring_simple`), and genuinely non-convex (`hat_non_convex`) — and now carries the corpus's **first genuinely concave point-in-polygon classification** (`HatMonotileExterior.v : hat_parity_classification`): the top-bump point `(17/4, 5√3/4)` is inside (crossing-number 1, odd; `HatMonotileInterior.v`) while the bottom **reflex-notch** point `(7/2, √3/4)` is outside (crossing-number 2, even; `hat_pocket_not_in_ring`) — a hull-interior exterior point that no convex polygon can present, classified correctly by the convexity-independent ray-parity test (not the JCT topological-interior equivalence, which stays out of reach for the non-convex hat). The **Spectre** monotile is both a non-convex 14-gon `Ring` and now the corpus's **second fully-mechanized concave family** (`SpectreConcaveFamily.v`): rational coordinates, `ring_simple` + `valid_polygon_spectre` (closing the deferred ~70-pair bash with no `sqrt 3`), a `cross`-based non-convexity certificate, and its first in/out ray-parity classification (`spectre_parity_classification` — interior `(5,1/2)` odd, concave-notch `(7/2,1/2)` even), parity with the hat; the Spectre's reflection-free *curved* edge — point-symmetric about its midpoint — is formalised separately in `SpectreCurvedEdge.v`. A third showcase opens the **Besicovitch–Kakeya** construction at its honest finite-stage level (`PerronStage.v`, Phase A of [`docs/besicovitch-kakeya-plan.md`](docs/besicovitch-kakeya-plan.md)): `perron_stage n : list Ring` is the polygonal Perron-tree elementary figure — the apex-fan over a unit base subdivided into `2^n` pieces — with exactly `2^n` closed, minimum-vertex, non-degenerate triangle rings (DCEL/ray-parity ready), the **direction-coverage** headline `perron_stage_directions_distinct` (the `2^n` triangles carry `2^n` pairwise *non-parallel* directions), unit-square containment, and a Phase-D hook proving those directions survive the area-reducing sliding translations. No measure theory is claimed — Lebesgue area → 0 is explicitly deferred to Phase D. **Phase B** (`KakeyaOverlay.v`) then lands the DCEL/overlay integration: each stage triangle is a `closed_chain` face-walk that `ring_of_chain` round-trips, and is **unconditionally `ring_simple`** (`perron_tri_ring_simple`, via `sip_shared_no_cross` — two non-collinear segments from a shared vertex never cross properly), so every triangle is a `valid_polygon` and a whole stage is a `valid_geometry` (`perron_geometry_valid`) — a legitimate `Overlay.boolean_op` operand. **Phase C** (`KakeyaExample.v`) freezes the depth-5 stage (32 triangles) as a regression anchor: thin near-collinear slivers of uniform area `1/32` that stay strictly positive, consecutive triangles sharing the apex cevian edge-to-edge (`perron_consecutive_share_cevian`), and the per-depth thinning `perron_area_decreasing` (`1/2^n` strictly decreasing) — the finite shadow of the deferred Phase-D `area → 0`. Finally, `KakeyaSlide.v` formalises the Perron **area-reduction** move itself, finitely: sliding the sub-triangles preserves direction coverage (`perron_slid_directions_distinct` — translation fixes each apex-cevian direction) and each piece's area (`perron_slid_area`), so total area can only drop through overlap — and `slid_pieces_overlap` exhibits a point interior to two slid depth-1 pieces, the reduction mechanism (the union-area arithmetic itself being the measure-theoretic Phase D).
- Companion modules (Real, Lattice, LineEq, etc.) ship alongside.

These feed the oracle consumed by [NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve).

See [`docs/HELP.md`](docs/HELP.md) and [`docs/READING-GUIDE.md`](docs/READING-GUIDE.md) for the documents that matter to your role (e.g. GIS Gus / BIM Bea → phase completion + audit files; Scholar Sam / Tech-Lead Tess → retros + proof-structure + seam maps; Newbie Nate → one completion doc + development-environment).


## Roadmap

### Phase 0–7: the NTS topological chokepoint

A multi-year plan to formally verify the load-bearing algorithms in
NTS — `RobustLineIntersector`, the noding pipeline
(`SnapRoundingNoder` + `MCIndexNoder`), and `OverlayNG` topology
construction — down to executable, provably-robust Coq-extracted code.
3–5 person-years of focused work; each phase is independently
publishable.

| Phase | Deliverable | Status | `NetTopologySuite.Curve` consumer |
|---|---|---|---|
| Simplifier *(warm-up, not in the chokepoint sequence)* | `Validate_binary64.v` — greedy perpendicular-distance simplifier on binary64 + RocqRefRunner | Qed-closed structural (14 lemmas); soundness bridge deferred | **100%** — `Robust.Simplify.GreedyPerpSimplifier`, 262 / 262 tests bit-exact against RocqRefRunner |
| 0 | `Orientation_b64.v` — Shewchuk-adaptive orientation under Flocq binary64 | Stage A filter Qed-closed (`b64_orient_sign_filtered`, decidability, totality, 5-constructor distinctness, NaN-safety); decoder consistency + cross_R soundness for integer regime `\|coord\| <= 2^25` Qed-closed (`Orient_b64_exact.v` — antisymmetry, all three vertex degeneracies, both cyclic permutations, headline `_sound_small_int`); Stage D expansion arithmetic now under construction (`B64_Expansion*`, `B64_FastExpansionSum*`, `Orient_b64_expansion.v`, `Orient_b64_stage_d.v` — sum-correctness Qed-closed, the general non-overlap headline a Tier-2 counterexample (false as stated — [`B64_Shewchuk_Thm13_counterexample.v`](theories-flocq/B64_Shewchuk_Thm13_counterexample.v)); specialised integer-safe headlines Qed-closed); **exact full-`binary64` orientation soundness now Qed-closed over the entire double-coordinate plane** (`Orient_b64_exact_full.v` — `b64_orient2d_exact_sound`, at three axioms, no `Classical_Prop.classic`), while the *fast* adaptive filter's general bounded-magnitude soundness (Stages B–D) stays deferred — see [`docs/soundness-strategy.md`](docs/soundness-strategy.md), [`docs/audit-shewchuk-stages.md`](docs/audit-shewchuk-stages.md) | **filter-complete** — `Robust.Orientation.RobustOrientation` (`Orient2d` / `Sign` / `SignFiltered` with 5-valued `OrientSignRobust`) bit-exact against RocqRefRunner `ORIENT` + `ORIENT_FILTERED` modes; `ORIENT_EXACT` provides the exact full-plane ground truth for the JTS #1106 differential test |
| 1 | `Intersect_b64.v` + `Intersect_b64_exact.v` — robust segment intersection, predicate + coordinate | **shipped end-to-end** — five-valued `IntersectSign` filter on top of Phase 0's `b64_orient_sign_filtered`; structural lemmas Qed-closed (decidability, totality, 10-way distinctness, NaN propagation); integer-regime cross_R soundness for both `IntersectNone` and `IntersectPoint` via the R-side `strict_completeness` theorem in `theories/Intersect.v`; intersection-point projections (`b64_intersect_point_{x,y}`) with a Qed-closed forward-error bound in `K·eps` / condition-number form + soundness typeclass; `IntersectCollinear` sub-case disambiguation is the only remaining gap — see [`docs/phase1-completion.md`](docs/phase1-completion.md), [`docs/phase1-c2-tight-retro.md`](docs/phase1-c2-tight-retro.md) | **complete** — `Robust.Intersect.RobustLineIntersector` (`SignFiltered`, `IntersectPoint*`) bit-exact against RocqRefRunner `INTERSECT_FILTERED` / `INTERSECT_POINT_*` modes, 187 / 187 differential cases including integer-regime adversarial family |
| 2 | `SnapRounding_b64.v` / `HobbyTheorem_b64.v` — formal model of Hobby 1999 + Halperin-Packer 2002 (ISR) | **milestones 1–4 landed** — hot-pixel layer (`HotPixel.v` + `HotPixel_b64.v`) through the segment-touches-pixel filter, the Liang–Barsky parameter-interval filter, the passes-through relation (+ tight half-open variant), the snap-rounding correctness invariant (`SnapRounding_b64.v`), and the topological-correctness theorem at the supported level (`TopologicalCorrectness_b64.v`); Hobby Theorem 4.1 stated as a Qed-closed conditional with Lemma 4.2 closed and Lemma 4.3's no-proper half a Tier-2 counterexample ([`HobbyCounterexample_b64.v`](theories-flocq/HobbyCounterexample_b64.v)) — see [`docs/audit-phase2-snap-rounding.md`](docs/audit-phase2-snap-rounding.md), [`docs/phase2-hotpixel-progress.md`](docs/phase2-hotpixel-progress.md), [`docs/hobby-theorem-proof-structure.md`](docs/hobby-theorem-proof-structure.md) | oracle modes `PASSES_THROUGH_FILTER` / `PASSES_THROUGH_HALFOPEN` extracted |
| 3 | `OverlayNG` — topology graph + boolean overlay with labelling | **conditional headline Qed-closed** — `valid_geometry` + `boolean_op` (`Overlay.v`), the planar `TopologyGraph` + `build_graph` + labelling + `correct_labels_all_ops` (`OverlayGraph.v`), the snap-rounding noding bridge (`OverlayBridge.v`), and `overlay_ng_correct_conditional` (`OverlayCorrectness.v`) under three named hypotheses (JCT, DCEL ring-assembly = `extract_rings_valid`, now conditional-Qed modulo the registered `H_bridge_core` seam, semantic bridge); JCT seam work in `PointInRing*` — the prior `geometric_interior_stdlib` formulation is **refuted as vacuous** (`JordanCurveSeam.v : geometric_interior_stdlib_vacuous`) and restated over continuous paths, with the headline **H1 re-pointed onto `geometric_interior_cont`** and the canonical `JCT_two_components_cont` hypothesis now carrying the inter-component **separation clause** (sufficiency proved by `jct_cont_interior_is_geometric`); the continuous-component spine (`JCT.v`) then proves the equivalence-relation + bounded-component-invariance algebra, so the trapped-interior separation `no_path_from_interior_to_exterior` is a **free Qed corollary** (the sketch's "thesis-scale core" is in fact free), isolating the genuine remaining seam to `parity_characterises_interior_cont` behind the non-vacuous headline `point_in_ring_correct_jct_cont`; the JCT itself stated not proved — see [`docs/jct-vacuity-finding.md`](docs/jct-vacuity-finding.md), [`docs/jct-proof-structure.md`](docs/jct-proof-structure.md), [`docs/h1-vacuity/`](docs/h1-vacuity/), [`docs/audit-phase3-overlay.md`](docs/audit-phase3-overlay.md), [`docs/audit-phase3-milestone5.md`](docs/audit-phase3-milestone5.md) | oracle mode `EDGE_IN_RESULT` extracted |
| 4 | Native circular-arc primitives (chord-approximation / Option B) | **conditional headline Qed-closed** — `CurveGeometry` types + `to_geometry` bridge, `inCircle_R` / `arc_orient` (`ArcOrient.v`), arc-chord / arc-arc intersection (`ArcIntersect.v`) with the IVT gap closed (`ArcIntersectIVT.v`), `arc_in_hot_pixel` (`ArcHotPixel.v`), sagitta machinery (`ArcChordApprox.v`), and `arc_overlay_correct_chord_approx` (`ArcOverlay.v`) under named hypotheses; **Flocq in-circle soundness** (`InCircle_b64_exact.v` — full-plane sign + `2¹¹` integer-regime value exactness, PR #146) and **arc-line Scope A** (`ArcLineIntersect_b64_exact.v` — first-stage `sP`/`sQ`/`dx`/`dy` before division); native (non-chord) circular arithmetic remains far future — see [`docs/audit-phase4-curves.md`](docs/audit-phase4-curves.md), [`docs/audit-phase4-chord-overfitting.md`](docs/audit-phase4-chord-overfitting.md), [`docs/issue-64-arc-primitives-triage.md`](docs/issue-64-arc-primitives-triage.md) | extracted oracle modes `INCIRCLE_SIGN` / `ARC_CHORD_CROSSES_CIRCLE` / `ARC_PASSES_THROUGH_PIXEL` (INCIRCLE backed by `b64_inCircle_B2R_sign_sound_small_int`) |
| 5 | Extraction toolchain + C# FFI to production NTS | pending Phase 1+ | 0% |
| 6 | Continuous integration of corpus against NTS test suite | pending Phase 5 | 0% |
| 7 | Soundness audit of curve-aware overlay operations | pending Phase 4 | 0% |

The "consumer" column tracks delivery on the C# side in
[NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve)
under `NetTopologySuite.Robust.*`.  100% means the algorithm is implemented,
its structural facts are mirrored as unit tests, and the implementation is
bit-exact with the Coq-extracted reference (RocqRefRunner) on every shipped
test case.  Full semantic soundness against the real-number model is a
separate axis — currently not claimed end-to-end on any phase.

The library audit for closing Phase 0 Stages B / C / D
(expansion-arithmetic refinement that resolves `OrientRUncertain`
into a definite sign) lives in
[`docs/audit-shewchuk-stages.md`](docs/audit-shewchuk-stages.md).
Bottom line: Flocq 4.2.2 ships TwoSum, Dekker's TwoProduct, and
Veltkamp splitting; the missing piece is Shewchuk's expansion
arithmetic on top of those.

The critical-path piece identified in the audit — a binary64↔ℝ
bridge for the `b64_plus` / `b64_minus` / `b64_mult` helpers — is
now Qed-closed in
[`theories-flocq/B64_bridge.v`](theories-flocq/B64_bridge.v).
Three theorems (`b64_plus_correct`, `b64_minus_correct`,
`b64_mult_correct`) each state that, under finiteness of operands
plus a no-overflow precondition, the operation's `B2R` equals the
exact rounded `B2R x ⊕ B2R y` and the result is finite.  Same
4-axiom set as the rest of the corpus.  This unblocks three
downstream targets that were each waiting on the same machinery:
the simplifier R-bridge, Stage A's arithmetic identities for
`b64_orient2d`, and Shewchuk Stages B / C of orient2d.

### Original targets (still relevant, partially complete)

1. **Segment intersection — completeness direction** — converse of
   `segments_share_point_implies_opposite_sides`. Given strict opposite-side
   conditions on both cross products, construct the intersection point
   via Cramer's rule and prove both parameters lie in (0, 1). Closes the
   full bidirectional robustness story for
   `RobustLineIntersector.computeIntersect`. Subsumed by Phase 1.
2. **Robust orientation predicate** — Shewchuk-style filter conditions.
   The keystone of the robustness story. Becomes Phase 0.
3. **Convex hull invariants** — `Convex.intersection_is_convex` covers
   the closure half; the constructive direction (vertices, lower
   hull, upper hull) is still open. The Brun-Dufourd-Magaud 2012 Coq
   formalisation is the proof-engineering template.
4. **DD arithmetic** — superseded by the Flocq-based path through
   `theories-flocq/Validate_binary64.v` and Phase 0.
5. **MIC center-is-interior** — for a non-degenerate polygon, the
   centre of the maximum inscribed circle lies strictly in the
   polygon's interior. Independent of the chokepoint work.
6. **Buffer corner relations** — for a positive buffer distance, the
   buffer of a convex corner consists of an arc whose central angle
   equals the exterior angle. Adjacent to Phase 4 (native curves).

### Progress log


      forall P0 P1 Q,
        b64_orient2d_safe P0 P1 Q ->
        match b64_orient_sign_filtered P0 P1 Q with
        | OrientRPos       => 0 < B2R (b64_orient2d P0 P1 Q)
        | OrientRNeg       => B2R (b64_orient2d P0 P1 Q) < 0
        | OrientRZero      => B2R (b64_orient2d P0 P1 Q) = 0
        | OrientRNan       => True
        | OrientRUncertain => True
        end.

  The "internal consistency" half of soundness: the five-valued
  sign decoder agrees with the sign of the rounded binary64 value.
  Same 4-axiom set, Qed-closed.

  The cross_R-valued soundness theorem -- relating the decoder's
  sign to the *exact* mathematical cross product -- is documented
  as a future target in the file's PROOF STATUS block.  It requires
  the Shewchuk Stage A forward-error theorem:

      Rabs (B2R (b64_orient2d P0 P1 Q) - cross_R_BP P0 P1 Q)
        <= b64_errbound_A_coeff_value * detsum

  which is the substantive proof slice (~1-3 days), needing per-op
  forward-error lemmas (`Plus_error.plus_error`, etc.) plus the
  accumulation analysis through the four `b64_minus` / two
  `b64_mult` / outer `b64_minus` chain.  Once that lemma lands,
  cross_R soundness follows mechanically by composition with the
  decoder-consistency theorem from this slice.

      Rabs (B2R (b64_op x y) - exact_op (B2R x) (B2R y))
        <= ulp radix2 (SpecFloat.fexp prec emax) (exact_op ...).

  Built on Flocq's `error_le_ulp` from `Core/Ulp.v`; unconditional
  (no normal-range precondition).  These are the per-step pieces
  the Shewchuk Stage A chain composition would eventually thread
  through the four `b64_minus` / two `b64_mult` / outer `b64_minus`
  structure of `b64_orient2d`.  Same 4-axiom set, Qed-closed.

      Theorem b64_orient_sign_filtered_sound_small_int :
        forall P0 P1 Q,
          orient2d_inputs_int_safe P0 P1 Q ->
          match b64_orient_sign_filtered P0 P1 Q with
          | OrientRPos       => 0 < cross_R_BP P0 P1 Q
          | OrientRNeg       => cross_R_BP P0 P1 Q < 0
          | OrientRZero      => cross_R_BP P0 P1 Q = 0
          | OrientRNan       => True
          | OrientRUncertain => True
          end.

  This is the cross_R headline the project was working toward,
  restricted to the integer regime: each input coordinate is integer-
  valued with `|coord| <= 2^25`.  In that regime every intermediate in
  the orient2d chain stays within binary64's 53-bit integer-exactness
  window, so `B2R det = cross_R_BP` *on the nose* -- no rounding error,
  no inequality.  Composes mechanically with the decoder-consistency
  theorem from `Orient_b64_sound.v`.  Same 4-axiom set, Qed-closed.
  The general bounded-magnitude regime remains an open Path 1.
(See the dedicated phase completion, audit, and retro documents listed in
the actor Reading Guide for the current detailed status. The full dated
forensic log of slices, consolidations, and openings has been moved to
the phase-specific docs and `docs/history/` to keep this README scannable
for all the defined actor roles (collapsed from initial 17 for overlap). Key high-level outcomes remain in the table above and
the phase docs; the complete session-by-session record is in the
retros and history/sessions/ for Scholar Sam / Tech-Lead Tess / Joost
the BDFL paths.)

- **registry framework (in force since the Stage D / Phase 2-3
  engagement)**: the Flocq layer's `Admitted` theorems are governed by
  the three-tier discipline described at the top of this README —
  `scripts/check_admitted.sh` plus the
  [counterexample](docs/admitted-counterexamples.txt) and
  [deferred-proof](docs/admitted-deferred-proofs.txt) registries — and a
  per-theorem axiom audit (`scripts/audit_axioms.sh` +
  [`docs/axiom-allowlist.txt`](docs/axiom-allowlist.txt) +
  [`docs/audit-exceptions.txt`](docs/audit-exceptions.txt)) tracks the
  `Classical_Prop.classic` footprint inherited from Flocq's binary
  arithmetic.  See [`docs/category-c-policy.md`](docs/category-c-policy.md).

## What this is NOT

- This is **not** a verified implementation of NTS. The C# code is not
  extracted from Rocq. The proofs are over an abstract model of points
  (pairs of reals) and the operations on them. If the C# implementation
  encodes the same mathematical operations, the proofs apply. If it does
  something subtly different (typical example: a fast-path that's not
  exactly equivalent on edge cases), the proofs don't catch it.
- This is **not** a substitute for unit tests. Tests cover behaviour the
  proofs don't reach: floating-point rounding, exceptions, performance,
  cross-platform consistency, interaction with the rest of the runtime.
- This is **not** complete. Current coverage is over 1,100 Qed-closed
  theorems across 67 `.v` modules (25 foundational Stdlib-only under
  `theories/`, plus Flocq-dependent work under `theories-flocq/`), with
  exactly 6 `Admitted` theorems (all counterexample; the deferred-proof
  registry is now empty), each registered in the counterexample registry
  (see the registries and `scripts/check_admitted.sh`).
  Coverage spans the algebraic foundations (real-number, vector, distance,
  orientation, line, disk, lattice, lex order), segment and bounding-box
  primitives, triangle / convex / centroid / reflection laws, the
  curve-linearisation stack (`Linearise.v` → `Simplify.v` → `Tin.v` →
  `Validate.v` → `Validate_decidable.v` + binary64 instance), and the
  early-to-mid phases of the chokepoint (orientation + intersection under
  binary64, snap-rounding foundations, overlay, chord-approximated arcs).
  The Phase 0–7 roadmap (below and in the actor Reading Guide) outlines
  what remains: full Stage D, open JCT / DCEL / Hobby pieces carried as
  deferred proofs or named hypotheses, and native (non-chord) curve
  primitives. Each phase ships independently with precise caveats; see the
  dedicated phase completion/audit docs for current status rather than
  this summary.

## Build

See [docs/HELP.md](docs/HELP.md) and [docs/READING-GUIDE.md](docs/READING-GUIDE.md) for which build path matches your actor/role (e.g. Newbie Nate vs. full Flocq for deep work). Also see [CONTRIBUTING.md](CONTRIBUTING.md) and [docs/FOR-AI-AGENTS.md](docs/FOR-AI-AGENTS.md).

### Local (macOS via Homebrew)

```sh
brew install rocq
rocq makefile -f _CoqProject -o Makefile.gen
make -f Makefile.gen
```

This builds the 25 foundational Stdlib-only modules in `_CoqProject`.
Modules with external dependencies (Flocq), plus the Stdlib-only Phase
3/4 modules built alongside them, live in `_CoqProject.full` and are
built inside the container only (see below).

CI (see [`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs the
host build on `macos-latest`, then:

- `scripts/check_admitted.sh` — the three-tier `Admitted` check across
  **both** `theories/` and `theories-flocq/`: every `Admitted` must
  appear in exactly one registry (counterexample or deferred-proof);
  `Axiom`, `Parameter`, and `admit.` are hard failures.
- `scripts/check_readme_axioms.sh` — verifies this README's axiom list
  matches `docs/axiom-allowlist.txt` verbatim.

A second CI job builds the `_CoqProject.full` corpus inside the pinned
Rocq 9.1.1 + Flocq 4.2.2 container with `make --output-sync=target` (so
each file's output stays contiguous), incrementally on pull requests —
unchanged files are restored from a content-addressed cache — and from
clean on every push to `main`.  The output-synced log is split into
per-file `Print Assumptions` chunks cached alongside the `.vo` they
were compiled with; `scripts/audit_axioms.sh` then audits the assembled
chunks of **every** project file against the allowlist (file-level
exemptions from `docs/audit-exceptions.txt`), and a missing chunk for
any file fails the build, so audit coverage never silently shrinks.

### Containerised build (Rocq 9.1.1 + Flocq 4.2.2)

For modules that need [Flocq](https://flocq.gitlabpages.inria.fr/) (the
`theories-flocq/` corpus, linking the validation, orientation,
intersection, snap-rounding, and overlay layers to IEEE-754 binary64)
the canonical environment is a podman container based on the
official `rocq/rocq-prover:9.1.1-ocaml-4.14.2-flambda` image with
`coq-flocq.4.2.2` pinned via opam. This matches the toolchain Boldo et al.
JAR 2015 §5 uses.

```sh
# One-time: build the image (~5 min, pulls + compiles Flocq under
# x86_64 emulation on Apple Silicon).
podman build -t nts-proofs .

# Build the corpus inside the image (uses the workspace COPY'd at
# image-build time, regenerates Makefile.gen from _CoqProject.full).
podman run --rm nts-proofs

# Iterate against the live workspace (volume-mount).  Note: clean
# host-generated build artefacts first via the .dockerignore-equivalent
# manual step, then regenerate.
podman run --rm -v "$(pwd):/workspace:z" -w /workspace nts-proofs bash -lc \
  'rm -f Makefile.gen* .Makefile.* theories/*.vo* theories/*.glob theories/.*.aux \
   && rocq makefile -f _CoqProject.full -o Makefile.gen \
   && make -f Makefile.gen -j2'

# Interactive shell for proof development with Flocq imports available.
podman run --rm -it -v "$(pwd):/workspace:z" -w /workspace nts-proofs bash
```

The host build is the canonical CI target (the macOS-arm64 runner has no
Flocq); the container is the augmented environment for modules whose
proofs need Flocq.

If the container path is blocked by your network policy (e.g. Debian
apt or `coq.inria.fr/opam/released` returns 403), see
[`docs/development-environment.md`](docs/development-environment.md)
for a host-install fallback that matches the container's package
versions exactly and builds locally on Ubuntu in ~5 minutes.

A successful `make` ends with `theories/*.vo` files and no errors. Each
`.vo` file is a kernel-checked term whose type is the corresponding theorem
statement. Build output also includes the `Print Assumptions` reports
(see top of this README).

## Licence

BSD-3-Clause, matching NetTopologySuite's licence. See [LICENSE](LICENSE).

NetTopologySuite is itself a derivative work of JTS Topology Suite, which
is dual-licensed under EPL 2.0 / EDL 1.0. The formal specifications in
this repository are derived from NTS source code; where that is the case,
the BSD-3-Clause grant respects NTS's attribution requirements.

## Contributing

See the full [CONTRIBUTING.md](CONTRIBUTING.md) (and the actor-specific guidance in [docs/HELP.md](docs/HELP.md) + [docs/READING-GUIDE.md](docs/READING-GUIDE.md) + [docs/FOR-AI-AGENTS.md](docs/FOR-AI-AGENTS.md) for agents).

The short version: new theorems must end with `Qed.` (or `Defined.`), respect the three-axiom + registry discipline, carry proper headers, and follow the documented session workflow for anything non-trivial. Joost the BDFL has final say on scope and borderline decisions. Pick your role card and contribute accordingly.
