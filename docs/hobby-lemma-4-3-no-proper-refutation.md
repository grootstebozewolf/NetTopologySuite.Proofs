# `hobby_lemma_4_3_no_proper` is false as stated — refutation

> **Status (this session).** The deferred-proof entry
> `hobby_lemma_4_3_no_proper` (carried with a 4-6 week "thesis-shaped"
> estimate) is **disproved by an explicit, Qed-closed counterexample**.
> The lemma moves from the deferred-proof registry to the
> counterexample registry. The headline
> `hobby_theorem_4_1_conditional` is unaffected (it only *assumes* a
> per-pair preservation hypothesis); what changes is that the corpus can
> no longer hope to discharge that hypothesis via the bare two-segment
> statement — closing Hobby Theorem 4.1 unconditionally needs the
> noded-arrangement hypothesis the deferred lemma had dropped.

File: `theories-flocq/HobbyCounterexample_b64.v` (Qed-closed).

## 1. The statement that is false

```coq
Lemma hobby_lemma_4_3_no_proper :
  forall (P0 P1 Q0 Q1 : Point),
    ~ segments_intersect_properly P0 P1 Q0 Q1 ->
    ~ segments_intersect_properly
        (snap_round P0 1) (snap_round P1 1)
        (snap_round Q0 1) (snap_round Q1 1).
```

Informally: "if two segments do not cross properly, neither do their
snap-rounded images." Quantified over **two arbitrary segments**.

`segments_intersect_properly P0 P1 Q0 Q1` (HobbyTheorem_b64.v §1) means
there exist parameters `t, s` *strictly* in `(0,1)` with
`segment_point P0 P1 t = segment_point Q0 Q1 s` — a crossing interior to
both segments. Note this is satisfied by any **collinear overlap**: a
point in the interior of the shared sub-segment has interior parameters
on both.

## 2. The counterexample (a "parallel collapse")

```
A = (0, 0.7) — (10, 0.7)     [horizontal at y = 0.7]
B = (3, 1.3) — ( 7, 1.3)     [horizontal at y = 1.3]
```

* **Before snapping.** `A` and `B` are parallel horizontal segments at
  *distinct* heights (0.7 ≠ 1.3), so they share no point at all — in
  particular `~ segments_intersect_properly A B`. (The `py`-equation of a
  proper crossing would force `0.7 = 1.3`.)

* **After snapping** to the unit grid (round-half-to-even):
  `0.7 ↦ 1` and `1.3 ↦ 1`, so both segments collapse onto the **same**
  grid line `y = 1`:

  ```
  snap A = (0, 1) — (10, 1)
  snap B = (3, 1) — ( 7, 1)
  ```

  These are now **collinear and overlapping** over `x ∈ [3,7]`. Their
  common interior point `(5, 1)` is reached at `t = 1/2` on `snap A` and
  `s = 1/2` on `snap B`, both strictly interior — a **proper
  intersection**.

So `~ segments_intersect_properly (originals)` holds while
`segments_intersect_properly (snapped)` holds: the lemma's conclusion
fails on this input. Coq witnesses:

```coq
Theorem hobby_lemma_4_3_no_proper_counterexample :
  exists P0 P1 Q0 Q1 : Point,
    ~ segments_intersect_properly P0 P1 Q0 Q1 /\
    segments_intersect_properly
      (snap_round P0 1) (snap_round P1 1)
      (snap_round Q0 1) (snap_round Q1 1).

Theorem hobby_lemma_4_3_no_proper_is_false :
  (forall P0 P1 Q0 Q1 : Point, ~ ... -> ~ ...) -> False.
```

The snap evaluations (`0.7 ↦ 1`, `1.3 ↦ 1`, integers fixed) are proved
through Flocq's `round_FIX_IZR` (the FIX(0) rounding equals `IZR` of the
integer rounding function) and `Znearest_imp` (round-to-nearest pins the
integer within distance 1/2).

## 3. Why the lemma is false — and the theorem still stands

Hobby (1999) Theorem 4.1 is a statement about a **fully noded
arrangement**: all pairwise intersections are already vertices, and
snap-rounding is applied to the resulting fragments. The deferred
`hobby_lemma_4_3_no_proper` dropped that context and quantified over two
*arbitrary* segments. Snap-rounding two arbitrary non-touching parallel
segments can pull them onto a single grid line, **manufacturing** a
collinear overlap. This is the textbook "snap-rounding merges nearby
features" phenomenon (cf. de Berg–Halperin–Overmars); it is precisely
what the noding hypothesis rules out and what the bare two-segment lemma
forgot to assume.

`hobby_theorem_4_1_conditional` remains **Qed-closed**: it merely takes a
per-pair preservation hypothesis `Hlemma43` as a premise and lifts it to
the arrangement. The refutation says: that premise is **not** provable in
the bare two-segment form the corpus had hoped (`hobby_lemma_4_3`, via
its load-bearing `_no_proper` half). A faithful unconditional Hobby 4.1
must instead carry the noding context — e.g. restrict the preservation
claim to pairs drawn from a `fully_intersected` arrangement, where the
collinear-collapse witness above is excluded because `A` and `B` would
already have been split / merged at noding time.

## 4. Registry effect

* **Deferred-proof registry** (`docs/admitted-deferred-proofs.txt`):
  remove the `hobby_lemma_4_3_no_proper` entry — it is not a tractable
  proof obligation, it is false.
* **Counterexample registry**
  (`docs/admitted-counterexamples.txt`): add
  `theories-flocq/HobbyCounterexample_b64.v:hobby_lemma_4_3_no_proper_counterexample`.
* `hobby_lemma_4_3` (the disjunctive composition in HobbyTheorem_b64.v)
  is still Qed-closed *as a file*, but it depends on the Admitted
  `hobby_lemma_4_3_no_proper`; since that Admitted is now known false,
  the composition proves a false lemma and must not be relied on. The
  recommended follow-up (a separate, larger task) is to restate the
  preservation lemma over noded arrangements and re-derive
  `hobby_lemma_4_3` from the corrected form. That restatement is flagged
  here, not undertaken in this session.

## 5. Bibliography

* J. D. Hobby, "Practical segment intersection with finite precision
  output," *Computational Geometry: Theory and Applications*
  13(4):199-214, 1999. §4.
* M. de Berg, D. Halperin, M. Overmars, "An intersection-sensitive
  algorithm for snap rounding," *Computational Geometry* 36(3):159-165,
  2007 — the merging-of-features phenomenon for arbitrary (non-noded)
  inputs.
