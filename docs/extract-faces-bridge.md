# The bridge discharge — `extract_rings_valid` R5, slice 3i (RED)

**Coq artifact:** [`theories-flocq/ExtractFacesBridge.v`](../theories-flocq/ExtractFacesBridge.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals trio, plus `Classical_Prop.classic` on the named re-point via
the Flocq dart-machinery lineage — `docs/audit-exceptions.txt`).

**Thread:** `extract_rings_valid` R5 — the second "What remains" item of
[`docs/extract-faces.md`](extract-faces.md) (slice 3g): *discharging the three
structural hypotheses of `ExtractFaces.extract_faces_valid` from the noder's
`fully_intersected` guarantee*, to re-point the registered deferred proof
`OverlayBridge.extract_rings_valid` onto the face extractor.

**Outcome:** **RED** — the discharge is blocked, and the block lands on the
hypothesis slice 3g's header and this session's prompt (R3/D1) both rated
"expected TRUE". The negative is machine-checked; the GREEN re-point is
deferred to a follow-up slice with the corrected hypothesis shape pinned below.

---

## Grep-first state

- `OverlayBridge.extract_rings_valid` (line ~486) is the **only** live entry of
  `docs/admitted-deferred-proofs.txt`. It quantifies over
  `OverlayGraph.extract` — the naive flatten refuted by
  `ExtractFlattenCounterexample.extract_unordered_not_valid` — so the re-point
  must restate the obligation over the *face* extractor.
- `ExtractFaces.extract_faces_valid` (slice 3g) discharges the obligation shape
  for `extract_faces` under three hypotheses on `D := result_darts op g`:
  (H1) `pairwise_no_proper_cross D`, (H2) per-vertex `fan_ok`,
  (H3) `no_short_faces D`.
- `result_darts op g := darts_of (result_edges op g) = E ++ map twin E`
  (`theories/ExtractFaces.v:74`, `theories/Dart.v:93`).
- `fully_intersected` (`theories-flocq/HobbyTheorem_b64.v:75`): distinct segments
  satisfy `~ properly_intersect \/ (shared endpoint)`.
- `pairwise_no_proper_cross` (`theories/RingSimple.v:47`) and `fully_intersected`
  speak about two **distinct but textually identical** constants
  `segments_intersect_properly` (Overlay's vs HobbyTheorem_b64's); they are
  convertible (`sip_overlay_iff_hobby`), so the noder→simplicity link is a pure
  renaming, *not* a geometric seam.

## RED — the prompt's R3/D1 premise is false

The prompt rated H1 the easy one ("D1, expected TRUE"), with the only subtlety a
lemma it assumed true: *"a segment does not properly cross its own reversal."*
**That lemma is false.** Under `segments_intersect_properly` (a common interior
point at parameters `t, s ∈ (0,1)`):

> For `e = (p,q)` with `p ≠ q`, the reversal `twin e = (q,p)` reproduces every
> interior point of `e` at `s = 1 − t`; the midpoint `t = s = 1/2` is a proper
> crossing.

`seg_properly_crosses_reversal` proves it. Two structural consequences, both
machine-checked:

1. **H1 is unsatisfiable for non-degenerate edges.** `darts_of` contains both
   `e` and `twin e` by construction; they are distinct darts (`twin_neq_self`)
   that properly cross, so `pairwise_no_proper_cross (darts_of E)` fails the
   moment any edge is non-degenerate:

   ```coq
   Lemma darts_of_nondeg_not_pairwise :
     forall (E : list Edge) (e : Edge),
       In e E -> fst e <> snd e -> ~ pairwise_no_proper_cross (darts_of E).

   Lemma pairwise_darts_of_forces_degenerate :
     forall E, pairwise_no_proper_cross (darts_of E) ->
       forall e, In e E -> fst e = snd e.            (* every edge is a point *)
   ```

   Tied to slice 3g's actual hypothesis:

   ```coq
   Lemma result_darts_nondeg_not_pairwise :
     forall op g e, In e (result_edges op g) -> fst e <> snd e ->
       ~ pairwise_no_proper_cross (result_darts op g).
   ```

   So H1 holds **only** in the all-degenerate regime — i.e. `extract_faces_valid`
   is vacuous on any non-trivial arrangement. This obstruction is **structural**:
   it depends on `darts_of` carrying twins, not on `fully_intersected`, and **no
   strengthening of `fully_intersected` can repair it.**

2. **`fully_intersected → pairwise_no_proper_cross` is false even on the
   undirected edge set.** The shared-endpoint disjunct of `fully_intersected` is
   *not* a "meet only at endpoints" guarantee: two distinct **collinear** edges
   sharing an endpoint (e.g. `(0,0)-(2,0)` and `(0,0)-(1,0)`) satisfy
   `fully_intersected` via that disjunct yet properly cross at `(1/2, 0)`:

   ```coq
   Lemma fully_intersected_not_pairwise_collinear :
     exists S, fully_intersected S /\ ~ pairwise_no_proper_cross S.
   ```

   The twin route gives the matching witness through `darts_of`:

   ```coq
   Lemma fully_intersected_darts_of_not_pairwise :
     exists S, fully_intersected S /\
               (exists e, In e S /\ fst e <> snd e) /\
               ~ pairwise_no_proper_cross (darts_of S).
   ```

(R1 "bigon" and R2 "fan collision" are the same degeneracy seen from the
`no_short_faces` and `fan_ok` sides: a `(p,q)`/`(q,p)` pair is a period-2 face
and an anti-parallel fan collision. They were not separately formalised — H1's
collapse already blocks the discharge, and all three failures share the one root
cause below.)

## The one root cause

`fully_intersected`'s shared-endpoint disjunct admits **degenerate collinear /
coincident configurations** — collinear overlaps, bigons, parallel fans — that a
real snap-rounding noder eliminates (it splits collinear overlaps at shared
points) but the *abstract predicate as written does not capture*. The missing
ingredient is a general-position / no-collinear-overlap condition. The prompt
anticipated such a "missing input" (`no_bigons` / `no_duplicate_geometry`) but
assigned it to H2/H3; in fact it is needed for H1 as well — **and even with it,
H1 over `result_darts` stays unsatisfiable because of the twin pairs.**

## GREEN — relocated, not discharged

`extract_rings_valid_faces_named` restates `extract_faces_valid` at the noded
labelled graph (over the *correct* extractor, not the refuted flatten),
Qed-closed by direct application:

```coq
Theorem extract_rings_valid_faces_named :
  forall (op : BooleanOp) (A B : Geometry),
    (forall v, fan_ok (outgoing v (result_darts op (noded_labeled_graph A B)))) ->
    pairwise_no_proper_cross (result_darts op (noded_labeled_graph A B)) ->
    no_short_faces (result_darts op (noded_labeled_graph A B)) ->
    forall poly, In poly (extract_faces op (noded_labeled_graph A B)) ->
      valid_polygon poly.
```

This is a **relocation** of the deferred obligation onto the corrected API, not a
discharge: its H1 is provably unsatisfiable for any non-degenerate output (§RED).
It is recorded so the follow-up slice composes its bridge in front of *this*
statement rather than the flatten's.

`extract_rings_valid_faces_holes_named` is the same relocation for slice 3h's
**with-holes** extractor (`ExtractFacesHoles.extract_faces_holes_valid`, which
landed on `main` in parallel). It carries the identical H1
(`pairwise_no_proper_cross (result_darts op g)`), so the with-holes re-point is
blocked on **exactly the same twin-pair obstruction** — the corrected discharge
plan below covers both extractors at once.

## The corrected discharge plan (for the follow-up slice)

Closing the bridge needs H1 **reformulated**, then re-derived — combinatorics
first, geometry second:

1. **Twin-aware simplicity.** Replace `pairwise_no_proper_cross D` with a
   predicate that excludes reverse pairs, e.g. quantifying over `e1, e2` with
   `e1 <> e2 /\ e1 <> twin e2`. This is satisfiable.
2. **No-twin-in-face (pure DCEL combinatorics, no geometry).** Prove a face ring
   of an `arrangement_ok` set with period `≥ 3` contains no dart together with
   its twin (a twin pair in a face walk is a spur, excluded by general position).
   Then `face_ring_simple` follows from the twin-aware predicate — re-proving
   `FaceRingSimple.face_ring_simple` without `ring_simple_of_subset D`'s
   full-`D` appeal.
3. **Non-collinear endpoint-share ⟹ ¬proper (geometry).** With a
   no-collinear-overlap strengthening of `fully_intersected`, derive the
   twin-aware predicate on the *undirected* survivor set. This is the genuine
   geometric step; the orthogonal-decomposition toolkit
   (`theories/Intersect.v`, `CurveJoinClassify.v` §1–2) is the starting point.
4. H2/H3 then follow from the same no-collinear-overlap condition (parallel-fan
   exclusion gives `fan_ok`; bigon exclusion gives `no_short_faces`).

Each of (2)–(4) is its own slice; the registry's `extract_rings_valid` stays
Admitted (naive-extract shape retained as the RED record per the registry's
rules), with the discharge plan now pointing here.

## Relation to the plan

- Closes the *investigation* of `docs/extract-faces.md` "What remains" item 2:
  the three hypotheses are **not** dischargeable from `fully_intersected` as
  stated; the true dependency structure is the four-step plan above.
- Does not touch R4 (Euler) or the analytic `hole_inside_outer` seam
  (`audit-rgr-comparison.md` §8) — separate squares, as the prompt directed.
- Branch: `claude/modest-euler-j81rk1`.

## Stopping condition hit

**TANGENT-STOP / productive COLLAPSE.** D1 did not stall — it was *disproven*.
Per the prompt's COLLAPSE clause, the witnesses are committed as Qed'd negatives
(the bridge's true shape is now machine-checked) and the wall is documented
precisely. D2/D3 (the strengthened bridge and the genuine re-point) are deferred
to the follow-up slice with the corrected hypothesis shape pinned above.
