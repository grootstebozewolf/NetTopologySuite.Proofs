# Archive — deferred-proof registry historical entries

> Forensic archive. These are the **closed / moved / superseded** narrative
> blocks lifted verbatim from `docs/admitted-deferred-proofs.txt` during the
> 2026-06-09 registry compaction. None of them is a live deferred proof
> anymore: each is either Qed-closed, or moved to
> `docs/admitted-counterexamples.txt` (false-as-stated). The registry now
> carries only the single live entry (`extract_rings_valid`) plus one-line
> pointers back to this file.
>
> Retained for institutional memory (the Joost / Scholar-Sam paths in
> `docs/READING-GUIDE.md`). Not parsed by CI.

---

## Slice A Piece 5b — Shewchuk Theorem 13 (`fast_expansion_sum_nonoverlap_shewchuk`)

> **Final disposition:** RECLASSIFIED 2026-06-08 → moved to
> `docs/admitted-counterexamples.txt`. FALSE as stated — the corpus's half-ulp
> `strict_succ_b64` is stronger than Shewchuk's bit-disjoint nonoverlapping;
> machine-checked counterexample in
> `theories-flocq/B64_Shewchuk_Thm13_counterexample.v` (see
> `docs/shewchuk-thm13-headline-counterexample.md`). The narrative below is the
> superseded deferred-proof rationale, retained for history only.

`fast_expansion_sum_nonoverlap_shewchuk` -- general unconditional
headline for Shewchuk Theorem 13 (1997, ~1 page of dense magnitude
analysis).  THESIS-SCALE.  Re-classified 2026-05-29 after 17 sessions
of cumulative work established the structural floor; previous estimate
of "3-4 sessions" did not survive contact with the Route 1 collapse
artifacts.  Reclassification rationale below.

WHAT IS QED-CLOSED in
`theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
  - `fast_expansion_sum_nonoverlap_shewchuk_general_conditional`:
    under `cascade_pathA_chain` on the initial state, the headline
    follows.  This is the load-bearing composition step; the
    "Work is composition, not new mathematics" path lands here.
  - `fast_expansion_sum_nonoverlap_shewchuk_two_singletons`:
    UNCONDITIONAL length-2 headline.
  - `fast_expansion_sum_nonoverlap_shewchuk_int_safe_singletons`:
    UNCONDITIONAL length-2 int-safe headline.
  - `fast_expansion_sum_nonoverlap_shewchuk_int_safe_two_pairs`:
    UNCONDITIONAL (2,2) int-safe headline.  Covers all practical
    orient2d-shaped Stage D inputs under `coord_int_safe`.

Plus the supporting machinery (200+ lemmas): cascade_invariant,
cascade_run, cascade_h_chain under Path A (pos + neg),
run_bound_step_preserves, b64_plus_int_exact + integer cascade,
compress structural lemmas, sort-by-abs Forall preservation, etc.

WHAT REMAINS OPEN -- the general unconditional headline only:
  Deriving `cascade_pathA_chain (initial_cascade_state x prov) rest`
  from the actual preconditions of the theorem, namely
    `fast_expansion_sum_safe e f /\
     nonoverlap_shewchuk e /\
     nonoverlap_shewchuk f`
  for arbitrary expansions `e f` (i.e. closing
  `_general_conditional` by discharging its `cascade_pathA_chain`
  hypothesis from these three assumptions rather than positing it).
  This is precisely Shewchuk Theorem 13's deep magnitude bookkeeping:
  per-element provenance tracking + cross-prov mixed-sign
  similar-magnitude case analysis + round-to-even boundary handling.
  Session 3 quantified the gap as "roughly 2^53 too loose" between
  the cascade invariant's natural bound and the h-chain link
  required for arbitrary inputs.

Session history (collapse artifacts in `docs/`):
  - Route 3 (descending strict_succ chain on input): ruled out
    2026-05-24 by `e=[4.0], f=[3.0]` counterexample.
  - Route 2 Session 2: clause (c) collapse on Form A state.
  - Route 1 design session: third design recommended.
  - Route 1 Sessions 2-12: cascade_state augmentation (Form B with
    cs_prov + per-source max), refined clauses, h-chain split as
    a separate cascade-step lemma; established the 2^53 gap
    structurally and Qed-closed the conditional headline.
  - Route 1 Sessions 13-16: integer-safe specialised headlines
    (the three UNCONDITIONAL Qed-closures listed above).
  - Route 1 Session 17 (`route1_attempt`, Aborted at length 3+):
    concrete demonstration of the deferred-proof obstacle inside
    the corpus.

PRACTICAL IMPACT.  For NetTopologySuite consumers, `_int_safe_two_pairs`
covers all orient2d Stage D inputs under coord_int_safe (the integer
geometry contract).  The general unconditional headline is a
theoretical completion (thesis-scale), not a practical blocker for
Phase 3 or downstream geometry correctness.

Estimate: thesis-scale (multiple months of focused magnitude
bookkeeping, comparable in shape to `hobby_lemma_4_3_no_proper`).
Not attempted in further single-session work without a published
magnitude-bookkeeping framework (Shewchuk §4-style provenance
tracking) to lean on.

---

## Phase 2 — `hobby_lemma_4_2`

> **Final disposition:** CLOSED (Qed). No longer Admitted; was retained in the
> registry only as historical context.

`hobby_lemma_4_2` -- CLOSED (Qed) in the predicate-fix + proof-attempt
session 2 sequence (May 2026).  Predicate corrected to strip-shaped
Minkowski sum per Hobby p.210 (see docs/hobby-lemma-4-2-session-1-
outcome.md "Design session outcome -- predicate fixed").  Proof
completed against the corrected predicate via product-sign case split
(`(px P1 - px P0) * (py P1 - py P0) >= 0` vs `< 0`), each branch
closing through IZR injectivity + R^- strip bounds + Rtotal_order on
`tp` vs `tq`.  Per-theorem `Print Assumptions`: only the two
README-allowlisted classical-reals axioms (no `Classical_Prop.classic`
pull, despite the file's overall audit-exceptions footprint -- the
proof avoids Flocq-bridge content).

---

## Phase 2 — `hobby_lemma_4_3_no_proper`

> **Final disposition:** MOVED to `docs/admitted-counterexamples.txt`. FALSE as
> stated. Refutation Qed-closed in `theories-flocq/HobbyCounterexample_b64.v`;
> see `docs/hobby-lemma-4-3-no-proper-refutation.md`.

`hobby_lemma_4_3_no_proper` -- MOVED to the counterexample registry
(docs/admitted-counterexamples.txt).  This was carried here as a
thesis-shaped (4-6 week) deferred proof.  It is in fact FALSE as
stated: the bare two-segment statement drops the noded-arrangement
context that Hobby Theorem 4.1 actually relies on.

Refutation (Qed-closed): theories-flocq/HobbyCounterexample_b64.v.
Witness -- two parallel horizontal segments at y = 0.7 and y = 1.3
(no shared point, so no proper intersection) snap-round to the SAME
grid line y = 1, becoming collinear and overlapping -- a proper
intersection manufactured by snapping.  See
docs/hobby-lemma-4-3-no-proper-refutation.md.

Closing Hobby Theorem 4.1 unconditionally requires restating
the preservation lemma over noded arrangements (a separate task),
not proving this two-segment form.

---

## Slice A — `cascade_pathAB_chain_from_nonoverlap`

> **Final disposition:** MOVED to `docs/admitted-counterexamples.txt`.
> Indischargeable — would close the false Shewchuk headline via conditional O8.
> See `docs/shewchuk-thm13-headline-counterexample.md` §Consequence.

`cascade_pathAB_chain_from_nonoverlap` -- MOVED to counterexample registry.
Indischargable: would close the false headline via conditional O8.
