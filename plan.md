# Plan: Advance Oracle Wishlist for Curve Awareness (JTS #1195 + NTS port) -- Fresh start (different task)

**Date:** 2026-06-21
**Branch:** grok/64-arc-continue-option-a (or current curve phase)
**Context:** The provided user query is the full "Oracle Wishlist for Curve Awareness" document. This is a **completely different task** from the previous plan (JCT Seam / Jordan cell fixes in RelateNG.v Coq proofs for triangle touch). 

Previous plan focused on Coq RelateNG falsehoods, counterexample registry, gtri cases for ii_cell, Jordan deferral in proofs corpus.

Current request: continue the RGR (Read-Red-Green-Refactor) process for curve TAGs in the oracle / NTS.Curve port. Document tracks accepted TAGs (D-PT/ARC_DISTANCE, C-LIN/ARC_CENTROID, D-AA/ARC_ARC_DISTANCE, OFF/ARC_OFFSET_XY, partial CP-PRED, etc.) based on C# analytical ports + oracle matches + unit tests. Many oracle modes + gens + Coq proofs (in theories/RelateCurve*, theories-flocq for b64, Arc* proofs) already exist for accepted items.

Evaluation: Overwrite plan.md entirely. Focus on proofs/oracle side work: pick next low-risk/cost pure-analytical TAG from wishlist, perform "Read" (grep code, tests, gens, driver, Coq theories), enhance/implement support (add cases to gens, pin more tests, extend Coq if gaps, update driver protocol if new mode needed), run verification (oracle_bin, gens, dotnet-style but here make + bash test scripts), mark ACCEPTED in wishlist doc with new "This run" section, update references.

**Decision:** Different task → fresh overwrite of plan.md. Discard old JCT/RelateNG text. Scope to oracle/proofs enhancements for remaining wishlist items. Prefer low-risk pure analytical (no noding/overlay core changes). Reuse existing arc math (ComputeCenter, DirectedSweep, invariants, ARC_OFFSET_XY, ARC_DISTANCE kernels, buffer assembly).

**Current state (to be re-verified in exec via reads/greps):**
- Oracle (driver.ml + extracted + gens): supports ARC_DISTANCE, ARC_CENTROID, ARC_ARC_DISTANCE, ARC_OFFSET_XY, ARC_SEGMENT_*, ARC_AREA_*, ARC_ARC_XY/SEGMENT_XY, BUFFER_REGION (used for ARC_BUFFER_SIMPLE via arc+chord ring), CURVE_RELATE_MATRIX, ring simple/point-in/holes for V-CP, many others.
- Generators: gen_arc_distance_tests.py, gen_arc_centroid.py, gen_arc_offset_tests.py, gen_arc_arc_distance_tests.py, gen_arc_buffer_simple_tests.py, gen_buffer_region_tests.py, gen_curve_relate_matrix_tests.py, etc. Produce .txt pins.
- Coq side: proofs for arc offset (ArcOffsetThreePoint, radial_offset), centroid (ArcCentroid.v), distance (ArcPointDistance.v, ArcDistance), area, length invariants, buffer region assembly (CurveBufferArea, CurveRingOffset, CurveOffsetAssemblyTotal), ring simple, point-in-curve-ring, relate for curves (RelateCurve*, RelateMatrixCurve*).
- Tests: arc_*_tests.txt, buffer_region, curve_relate etc. oracle_bin runnable.
- Many TAGs ACCEPTED on C# side per doc (D-PT lift to CS/CC Point, C-LIN for CS, D-AA leaf, OFF leaf, partial CP-PRED lifts for Covers/Intersects/Dist on shell).
- Still wishlist / partial: ARC_BUFFER_SIMPLE (gen exists but "still wishlist"), full COMPOUND_ARC_DISTANCE (Point delegate done, full compounds + non-pt wishlist), exact BigDecimal/adversarial RGR harness for curves (no full ROCQ_REF_BIN diffs wired yet), full V-CP analytical, IsSimple/IsValid for curves, CURVE_RELATE full, robust intersect, noding, buffer full, simplify on arcs.
- RGR pattern from doc: extensive "Read" (grep on fallbacks, enumerator, existing analytical, tests), add Red failing-intent test (C# or here gen/assert that would fail without analytical), Green minimal impl/lift, Refactor (tiny, comments, match Length pattern), verify tests + oracle probes match, mark ACCEPTED if all green + bit-exact.
- In proofs repo: can do analogous for enhancing gens/tests, Coq lemmas, driver if needed. Run gens to refresh .txt, invoke oracle_bin, check diffs or protocol.
- Build: make in oracle/, scripts like gen_*.py > tests.txt , oracle_bin execution.
- Previous work in session: JCT fixes landed, arc review fixes; now pivot to curve oracle wishlist continuation.
- No new Admitted in Coq beyond registered; 3-axiom limit for new proofs.
- Oracle protocol is text stdin modes like "ARC_DISTANCE", "ARC_OFFSET_XY", "BUFFER_REGION".

**Goal of this planning session:**
- Pick one concrete next low-risk/cost TAG from wishlist (e.g. ARC_BUFFER_SIMPLE completion/enhancement or full low-risk V-CP predicate wiring or IsSimple curve ring using existing arc intersect).
- Plan "Read" investigation (grep + read specific files for buffer, offset assembly, ring simple, CP, driver protocol, relevant .v files).
- Plan enhancements: extend gen for more adversarial/degen/negative/compound cases; pin more exact matches; add Coq support/lemmas if gap; ensure oracle_bin produces correct for new pins.
- Plan update to the wishlist doc itself (add "This run" RGR section, mark ACCEPTED based on verification).
- Update related (TRIAGE, _CoqProject comments, oracle README if any).
- Verification: run gens, oracle tests, make, check scripts, perhaps simulate RGR with new test cases that would fail without the feature.
- Keep scope: pure analytical/structural where possible. Build on existing (ARC_OFFSET_XY, buffer assembly proofs, arc kernels).
- Output: updated plan.md, then (after exit) execution that produces code/doc changes + passes checks.

**Risks / constraints:**
- Prefer items with existing oracle mode + some Coq backing (e.g. buffer simple uses proven offset + assembly).
- Do not implement high-risk noding/overlay changes here.
- For C# side work described in doc, note that proofs/oracle is the reference; plan focuses on enhancing the reference side or generators to unblock more RGR on NTS side.
- Exact transcendental (length/area/centroid/offset) use interface-boundary float + exact invariants (like ARC_*_INVARIANTS_EXACT).
- Adversarial + NaN/huge/near-collinear coverage.
- After changes: gens must be re-runnable; tests.txt updated; oracle_bin agrees.
- No breakage to existing accepted modes/tests.
- If picking relate/V-CP: reuse existing curve relate matrix gen + ring predicates.

## Phase 0 — Investigation / Read (fresh for this task)

**Actions:**
- Grep extensively in oracle/ (driver.ml, gen_*.py for buffer/compound/relate/ring, *_tests.txt) and theories/ (RelateCurve*, Arc*, Buffer*, Offset*, Ring*) + TRIAGE_NTS_JTS_ISSUES.md for current state of ARC_BUFFER_SIMPLE, COMPOUND_DISTANCE, V-CP (IsSimple/ring simple/point-in/holes), CURVE_RELATE.
- Identify exact gaps vs wishlist (e.g. does gen_arc_buffer_simple cover collapse/negative/degen + verify emitted ring is valid curve ring + area/distance invariants? Compound distance full?).
- Read driver protocol sections for BUFFER_REGION, ARC_OFFSET, distance modes.
- Read gen_arc_buffer_simple_tests.py + arc_buffer_simple_tests.txt + related buffer gens.
- Read relevant Coq (e.g. CurveRingOffset, CurveBufferArea, arc offset proofs, any ring simple for curves).
- Note any TODOs or "still wishlist" comments.
- Confirm oracle_bin exists and is runnable.

**Deliverable:** Notes (in thinking or temp) on gaps; choose specific next TAG (recommended: ARC_BUFFER_SIMPLE as "low-risk entry to buffer" + uses existing OFF + assembly; or "IsSimple for curve rings" if simpler).

## Phase 1 — Pick next TAG + plan RGR cycle (adapted to proofs/oracle)

**Picked (example; confirm in exec):** ARC_BUFFER_SIMPLE (or enhancement to full BUF-1 single-arc via offset + round cap assembly + degen handling). Rationale: explicitly "Low-risk entry to buffer" in wishlist; builds directly on recently accepted OFF (ARC_OFFSET_XY) + proven buffer assembly (no new noding); oracle mode composed via BUFFER_REGION on arc+chord already has gen; high leverage for BUF; easy to pin more cases + mark more of it ACCEPTED.

Alternative if buffer already solid: pick "more predicate wiring (Relate) for curves" or partial IsSimple using ARC_ARC_XY + ARC_SEGMENT_XY.

**RGR cycle (proofs/oracle analogue):**
- **Read (reference):** Grep + read (as Phase 0) on current Linearize fallbacks in related, enumerator usage, existing analytical (offset, distance, intersect for validity), test patterns in gens, how BUFFER_REGION / ARC_BUFFER_SIMPLE pins work, what C# side expects (from doc).
- **Red:** Add/enhance test cases in gen_arc_buffer_simple_tests.py (or new) + assertions that would fail without full analytical single-arc buffer (e.g. emitted boundary has offset arc preserved, degen->empty or null, area invariants, distance to interior of buffer == |d| for +d on unit arc, negative collapse cases, adversarial near-collinear arc for offset). Make some "would be approx only under linearize".
- **Green:** Minimal enhancements:
  - Extend generator to emit more curated + sweep adversarial for single-arc buffer (positive/negative d, degen radii, collinear input).
  - If protocol gap: add explicit "ARC_BUFFER_SIMPLE" mode wrapper in driver.ml if beneficial (currently via BUFFER_REGION on 2-seg); or just improve the pin data.
  - Add/strengthen Coq side if gaps (e.g. lemmas for single-arc buffer region producing valid CurvePolygon shell, or exact area for the lens case). Reuse CurveOffsetAssembly, round join, offset preserve.
  - Update arc_buffer_simple_tests.txt by running the gen (or manual pins from oracle_bin runs on key cases).
- **Refactor:** Keep tiny (no over-engineering; comments citing epic §7, RGR, match to Length/Offset patterns); ensure composes for Compound/CurvePolygon later.
- Run: python gen... > tests.txt ; invoke oracle_bin on samples; verify matches + invariants.

**Deliverables for phase:**
- Updated generator + fresh .txt with more coverage.
- (If needed) small driver or Coq addition Qed.
- New entries or expanded in wishlist doc under a "This run: Picked TAG ARC_BUFFER_SIMPLE ..." section, with RGR steps, "Accepted based on ..." (tests green, oracle match on probes, e.g. +d emits concentric arc at r+d, degen null, area == pi*(r+d)^2 - pi r^2 adjusted for partial? for full circle case).
- Mark as partial or full ACCEPTED in "Current Oracle Modes Used" and wishlist.

## Phase 2 — Verification & doc sync

- Run relevant: make (if Coq), oracle/Makefile targets, gens, bash scripts for arc/buffer tests.
- `oracle_bin` direct probes for key cases (e.g. unit arc +d, collapse).
- Update wishlist.md (the provided doc) : add This run section, update ACCEPTED lists, "Next TAG recommendations" if advanced, cross-refs.
- Update TRIAGE_NTS_JTS_ISSUES.md or related if curve buffer status changes.
- Check no breakage: run broader curve tests if scripts allow.
- If picking relate/V-CP: similar for gen_curve_relate_matrix or ring_simple gens + pins.
- Optional: add a small "exact ref" note or more adversarial in gen.

**Files likely edited:**
- oracle/gen_arc_buffer_simple_tests.py (or equivalent for chosen TAG)
- oracle/arc_buffer_simple_tests.txt (regenerated)
- oracle/driver.ml (if new explicit mode or helper)
- theories/ (any new/strengthened lemma for buffer/ring/relate)
- The wishlist document itself (update status sections, add "This run")
- Possibly oracle/curve_polygon.py or buffer gens, test_*.ml
- docs / TRIAGE if status updates

## Phase 3 — Next steps / iteration prep

- After this TAG, recommend next from remaining (e.g. full COMPOUND_ARC_DISTANCE lift, IsSimple curve, more CP predicates, V-CP full analytical location).
- Note any remaining wishlist items (exact BigDecimal ref harness for curves, adversarial RGR diffs, full noding).
- Ensure all changes allow re-running gens and oracle_bin agreement.
- Tie back to JTS epic TAG table.

## Overall Implementation order (incremental; verify after each)

1. Phase 0 investigation reads/greps (document gaps).
2. Pick concrete TAG (ARC_BUFFER_SIMPLE preferred for low-risk buffer entry; confirm or switch to V-CP predicate if simpler).
3. Red: extend gen + add test cases/asserts that exercise analytical path.
4. Green + minimal Coq/driver if needed; run gen to update pins.
5. Refactor + comments.
6. Full verification: gens, oracle_bin runs on new pins, broader curve tests, build.
7. Update wishlist document with RGR narrative + ACCEPTED marks.
8. Sync other docs (TRIAGE, etc.).
9. Re-run check scripts if applicable (admitted not central here; focus oracle tests).
10. Edit this plan.md to mark progress.
11. (Optional) prepare for next TAG in recommendations.

## Verification (success criteria)

- Chosen TAG has expanded test coverage in gen + .txt.
- oracle_bin produces expected outputs for new/curated cases (exact match on probes like offset arc controls at r+d, buffer emitted ring valid, area/distance invariants hold for simple cases).
- No breakage to existing ARC_*/BUFFER modes (re-run gens + compare or targeted).
- Wishlist document updated with new "This run" section describing Read/Red/Green/Refactor + "Accepted based on tests (green, oracle matches)".
- "Current Oracle Modes Used" list reflects any new/expanded.
- If Coq changed: proofs compile (make in relevant), no new unregistered Admitted.
- Scripts like gen_*.py succeed; oracle/oracle_bin executable runs the modes.
- Clean git diff focused on the TAG (gens, pins, doc update, minimal code).
- Follows guiding principles: low risk/cost, pinnable to oracle mode, pure analytical preference.

## Risks / notes specific to this task

- Transcendentals (area, length, offset dist) handled via invariants + one interface-boundary float (consistent with existing ARC_LENGTH, ARC_CENTROID, ARC_OFFSET).
- Degen/collapse/negative/NaN/huge must be covered (oracle distinguishes DEGENERATE/EMPTY/NAN).
- For buffer: assembly (offset arcs + joins + chord handling for degen) already has proofs; focus on single-arc case + gen pins.
- Compound lifts (e.g. min over arcs for distance) may be partial (delegate per member) -- note as such.
- No changes to core noding/overlay in this scope.
- The RGR in doc is often C# port + oracle verification; here analogous is gen/test pin + Coq ref verification.
- If oracle_bin not up-to-date, may need make in oracle/.
- After push/PR in prior, now focus on curve wishlist continuation.

## How this advances the epic

- Unblocks more low-risk TAGs on NTS.Curve (BUF-1 foundation, more predicates).
- Strengthens RGR harness (more pins, better adversarial).
- Documents progress in the wishlist itself.
- Prepares for higher (relate matrix full, noding) by having solid analytical primitives.

This plan is scoped to the provided wishlist document as the task input. Execute phase-by-phase, always updating the wishlist doc when accepting a TAG. Use extensive Read (grep/read) before Red/Green.

(Previous JCT/RelateNG/Coq seam text discarded as unrelated.)


## This run outcome (oracle expansion)
- ARC_BUFFER_SIMPLE: dedicated mode + exercised in its gen (parity vs BUFFER_REGION path).
- CURVE_RELATE: input stabilized (already wired; pins via gen).
- ARC_SIMPLIFY_DECISION + ARC_OFFSET_FILTERED: stubs + expanded basic pins (5+ cases) + active Makefile probes.
- ratchet holds (allowlist updated for buffer refactor + filtered).
- oracle_bin rebuilt; main gens + new targets pass.
- pins refreshed; wishlist updated.
(Partial: full adversarial gens for stubs left for next RGR; plan updated here.)

## Observatory paragraph (big-bang unified Buffer pilot + Slice 3)
Buffer is now natively supported via the unified architecture (IGeometrySegment + GetSegments() + GeometryOperationDispatcher/BufferOp). One code path iterates the segment list for *all* input geometry kinds (Linear/CircularString, CompoundCurve, Polygon, CurvePolygon). When any CircularArcSegment is present the analytical leaves (ARC_OFFSET_XY homothety from proofs, CurveRingOffset segment-wise, round joins/caps, CurveBufferArea algebra) are used directly; no Linearize/Flatten fallback and no per-type branches. Output type is CurvePolygon precisely when the input carried arcs (with proper hole/collapse/endcap rules); pure-linear inputs continue to hit the legacy path (zero regression). Multi* (Slice 3) delegates via recursion in GetSegments() + dispatcher (recurse members, assemble, preserve CURVE if any arc). The proofs/oracle side already had the segment model at ring level (CurveSegment) and offset assembly; the big-bang lifts it to top-level Geometry segments in NTS with dispatcher. Buffer matrix row now driven by # coverage: tags (Arc/CS/CC/CP/Multi ⚠️ via red_buffer_unified + region/arc tests + ncomps protocol in BUFFER_UNIFIED). Dovetailed with dashboard PR #274 (parser + tags). RGR per slice: Read (oracle + unified review), Red (multi-comp + holes tests), Green (ncomps dispatch in driver.ml), Refactor (matrix notes). Review nits addressed (exact is_closed, multi \n sep, header, docstring); PR #275 open/clean + CI green post-push. See red_buffer_unified_tests.py, driver.ml run_buffer_unified, arc-offset-red-test-example.cs, updated COVERAGE_MATRIX, dashboard, plan.md.

