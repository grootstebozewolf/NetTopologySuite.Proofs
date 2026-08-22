# Retire #67 — second pass

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** three of the four preconditions below — ADR-0003 unconsumed by the capstone, **#523** open, **#503**'s four defects uncorrected. Precondition 1 is largely met by **#530**. See [Retire #67 — RelateNG](closed/07-retire-67-relateng.md) for why the first pass declined to close.

> **Note, 2026-08-22.** #67 was briefly closed by accident: the ticket-07 commit's
> subject line contained the substring `close #67` (in the phrase "decide NOT to
> close #67"), which GitHub read as a directive. Reopened, with the convention
> recorded in [`docs/agents/issue-tracker.md`](../../agents/issue-tracker.md).
> The decision to keep it open was never revisited.

## Question

The first pass decided **not** to close #67: its compute path returns confidently
wrong matrices with no marker, and four classifiers are `Prop := True`. Closing
then would have been an overclaim. This ticket asks the same question once the
blocking defects are gone: **does #67 close, and where does its residue go?**

Preconditions to check before re-deciding — each is a specific, checkable fact:

1. **#522 fixed** — *partially met as of 2026-08-22 (#530 merged).*
   - ✔ `RelateNGCore.v:337` no longer answers `ll_matrix_disjoint`; it returns
     `DE9IM.im_unsupported`, and `im_unsupported_no_predicate` proves that
     sentinel supports none of the ten `RelatePredicate`s.
   - ✔ `triangle_pair_regime` returns an explicit unsupported sentinel — the new
     `TPR_Unsupported` regime — so overlapping triangles are no longer
     misclassified as disjoint.
   - ✘ The four `Prop := True` classifiers in `RelateMatrixTriangle.v` are
     **still vacuous**. They now carry machine-checked vacuity witnesses
     (`classify_overlap_holds_of_a_separated_pair` and siblings), so they cannot
     be *cited* as content — but `TPR_Overlap` is still unreachable, which is
     #522 item 2 and needs real predicates over `gtri`. The layering note in that
     file was wrong and is corrected: `GeneralTriangleSeparation` does not import
     it, so the import needs no refactor.
   - ~ `prepared_evaluate_agrees` is still `reflexivity` over the stub, but
     `evaluate_ignores_cache` now proves the cache is never consulted — the gap
     is machine-checked instead of implied. #522 item 3.
2. **ADR-0003 actually consumed.** The two-tier model is declared; check that the
   nine-cell capstone work uses it — BI and side-E\* specified against the *open*
   interior and reached through the bridge, rather than re-deferred. Today: 3/9
   cells for triangle touch (II `RelateNGTouchCells.v:204` guarded, BB `:337`, EE
   `:54`), 2/9 for rect touch (EE `RelateNGRect.v:160`, II `:305`).
3. **#523 resolved or explicitly accepted.** `CURVE_RELATE_MATRIX` distinguishes
   `F` (proven empty) from not-computed, or the epic records that its one
   geometry-compute mode cannot yet be used as a differential reference.
4. **The four documentation defects** from #503 corrected, since two of them
   (`issue-67-relateng-triage.md:296`, `verified-claims.md:851`) *understate* what
   is proven and would make the closure evidence look thinner than it is.

Residue that will still need placing at that point, none of it blocking:

- The nine-cell capstone remainder, whatever ADR-0003 leaves.
- Multi-geometry / mixed-dimension relate — nothing exists beyond
  `RelateNodingLineLineCollection.v`'s `list Segment2` cross-products, and
  `RelateNGCore.v:337` is the general case.
- A cache-*consulting* prepared `evaluate` (ask #5).
- `DE9IM.v`'s recorded incompleteness witness
  (`disjoint_intersects3_example_holds:458` — one matrix satisfies both `disjoint`
  and `intersects₃`). Decide whether that is a permanent caution or an ask.

Do **not** re-litigate: the II-cell guard is maximal (`RelateNGTouchRED.v:170`,
Qed) and `touch_int_ext_exclusion` (`RelateNGTouch.v:200`) is unconditional. Both
are results.
