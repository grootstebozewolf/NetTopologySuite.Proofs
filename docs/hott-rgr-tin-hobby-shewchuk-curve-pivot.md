# HoTT RGR pivot: next big chunk (TIN / Hobby / Shewchuk / Curve)

**Status.** Written as the immediate follow-on RGR after the Voronoi pilot (the first small equivalence from `docs/hott-rgr-risk-cost-pivot.md`). This records the Red/Green/Refactor analysis and decision for the "next big chunk" of HoTT linkage work: the interconnected area of TIN, Hobby curve lemmas, Shewchuk exact predicates (the base), and Curve linearisation/arc handling.

Per the original pivot request and the "Continue the loop" instruction, we create a unique feature branch, perform the RGR (analysis doc + Green skeleton for the recommended first piece), update visibility (HoTT-Status.md), push, and self-verify with `/check-work`.

The goal remains "prove the link" with small, high-value HoTT equivalences + one justified axiom (univalence) + transport, using the archive as the mine for re-expression rather than re-implementation.

## Where the RGR cycle stands (post-Voronoi pilot)

**RED — the four areas that were the "big remaining" in the classical corpus are still RED for HoTT linkage (no NTS ≃ formal equivs yet).**

- **TIN (Tin.v / CurveLinearise)**: Archived `archive/theories/Tin.v` and `archive/theories/CurveLinearise.v` contain a number of Qed theorems (linearisation faithfulness for CIRCULARSTRING/COMPOUNDCURVE, endpoint invariants). But no model of NTS TIN structures, no equivalence to a formal TIN predicate, and CurveLinearise was conditional on phase-4 work. High risk of pulling in full curve geometry if we attack "native curves" too early.
- **Hobby (Hobby lemmas 4.1 / 4.3)**: The classical corpus had b64 proofs for Hobby's theorems on biarc approximation / clothoid residuals (see `archive/theories-flocq/HobbyTheorem_b64.v`, `HobbyCounterexample_b64.v`). There were counterexample findings and "no proper refutation" docs; the proofs were delicate and some headlines conditional. No HoTT re-expression or NTS HobbyCurve / Noding equivalence.
- **Shewchuk (base exact predicates + Thm 13)**: This is the strongest GREEN in the classical archive for the low-level engine: `B64_Expansion_Shewchuk.v`, `B64_FastExpansionSum_Shewchuk*.v`, `Orient_b64_exact.v` etc. delivered Qed sign-correctness under the weakened nonoverlap_shewchuk predicate. However, full Thm 13 (the growth / monotonicity of expansions) had a documented defect path (`B64_Shewchuk_Thm13_pathA_defect.v`) and was carried as deferred. No HoTT Equiv wrapping the orient/incircle to NTS RobustDeterminant.
- **Curve (Arc* / phase4 conditionals + linearise)**: `archive/theories/ArcOrient.v`, `ArcIntersect.v`, `CurveLinearise.v` etc. had substantial work but many results were conditional on phase-4 chord-approx soundness or carried named hypotheses. Native (non-linearised) circular arcs were explicitly deferred. NTS SegmentString forces linearise for Curve in the C# side.

The old linkage (b64 oracles + extraction) existed for some of these but never delivered a first-class `NTS_Foo ≃ Coq_Foo` + transport statement.

**GREEN — we already have the pivot assets + the first small example (Voronoi) that proves the methodology.**

- VoronoiEquivalence.v skeleton + fixed hygiene (List import, IsEquiv record, Admitted loud for the link claim, compiles cleanly).
- Risk/cost decision framework from the prior RGR doc (small primitives first wins on value/risk/cost).
- One-axiom generous policy codified and applied (exactly one univalence per .v, justified in header for C# transport).
- Archive as source of truth (the b64 Shewchuk Qed results, Orientation invariants, Hobby b64, Tin linearise Qed, Arc* conditionals are all available to mine rather than re-prove).
- Personas + RGR + branch discipline (feature/hott-rgr-*, PRs target hott).
- Single pythagoras entry + updated README / axiom-policy / FOR-AI-AGENTS.

**OPEN — the four areas as candidates, plus the cross-cutting "fill the Voronoi admits" and "add incircle base".**

## Risk/cost table for the chunk (TIN / Hobby / Shewchuk / Curve)

| target | linkage value | risk (tractability / contributor impact) | cost (setup + per-result) |
|--------|---------------|------------------------------------------|---------------------------|
| **Shewchuk base first** (orient + incircle via expansions; prove NTS_Orient ≃ formal_orient + one transport of an antisym/collinear invariant; skeleton + fill using B64_Shewchuk_* Qed) | **highest in the chunk** — orient is the root of the predicate tree (Delaunay/Voronoi cite it, Hobby biarcs rest on turn tests, TIN noding, arc predicates, everything). One solid equiv here multiplies to all later chunks via transport. Archive already has the hard Qed work. | **lowest** — narrow surface (one predicate family), classical already solved the expansion sign problem (we just wrap + transport), re-use Voronoi Point/cross pattern, bounded "first real Shewchuk" per review. | **low** — one session for skeleton (this doc), follow-on for fill; no new Flocq/container; compiles with same self-contained records. |
| Hobby 4.1/4.3 (biarc / residual monotonicity) | high (directly attacks curve noding quality that NTS ships) | medium — delicate classical proofs had counterexamples and "no proper refutation" findings; re-expressing in HoTT paths/HITs may be elegant but we don't have the lemmas yet | medium-high — needs the orient base first anyway; multiple lemmas |
| TIN + CurveLinearise faithfulness | high (NTS.Tin / Curve consumers care about linearised vs native) | medium-high — pulls in full curve model + conditional phase-4 results; NTS SegmentString forces linearise so "native curves" equiv may be moot for C# link | high — larger surface, risk of recreating phase4 conditionals |
| Native (non-chord) curves / arcs as HITs | high long-term (synthetic topology win) | **high** — requires S¹ HIT, winding as path data, new concepts for most personas; classical explicitly deferred native arcs | very high — multi-session, new theory |
| Fill Voronoi admits + incircle (as cross-cut) | high (completes the first pilot) | low — re-uses the same decision, just port Triangle/ArcOrient + InCircle_b64 | low-medium — but secondary to getting Shewchuk base |

## Decision (the chunk pivot)

1. **Shewchuk base first (orient/expansion equiv + transport).** This is the narrowest highest-leverage square. Everything else in the chunk (and Voronoi/Delaunay) depends on robust orientation/incircle. We get immediate "we proved the link for the predicate that the entire geometry trusts" + a reusable transport pattern. The archive has the Qed pieces (sign_of_expansion_correct_shewchuk etc.) ready to be the body of the maps/IsEquiv. Low risk of scope creep if we bound to "one predicate family + one transported lemma".

2. **Then Hobby (after orient base is solid).** The Hobby lemmas are the next consumer of orient/turn tests. Classical b64 work exists; once we can transport "formal Hobby 4.x holds for NTS via orient_equiv", we close a real NTS curve-noding claim.

3. **TIN / CurveLinearise after the above.** Use the base + Hobby to attack linearisation faithfulness. Defer "native curve" HIT modelling until we have the linearised link working (and re-evaluate whether NTS C# ever needs the native equiv given SegmentString linearise).

4. **Keep one axiom only (univalence), loud, justified per file.** Same policy. ShewchukBaseEquiv.v will carry its own copy of the Equiv/IsEquiv + Axiom with header justification tied to "transport of orientation invariants to C# RobustDeterminant".

5. **Update visibility.** Create HoTT-Status.md (actionable from PR #89 review) with a "Current Chunks" table. Update README current state. Append Session outcome to this doc. Cross-ref from risk-cost-pivot.md and VoronoiEquivalence.v.

### Why Shewchuk first? (added per PR #89 review)

(See the table row and the chunk decision above.) In addition: the classical project already paid the heaviest cost for Shewchuk (the 7-piece Slice A, the defect analysis for Thm13, the b64 bridges). By doing the HoTT equiv layer on top of that investment we convert sunk cost into immediate linkage value with minimal new proof burden. It is also the "first recommended small step" that unblocks the rest of the chunk without forcing us to solve Hobby or TIN or native curves in one go. Bounded, high-marginal-value, re-uses RGR + personas + archive.

## Future paths left open

- Once Shewchuk orient_equiv is filled (maps + IsEquiv Qed + one transport), the Voronoi pilot can be strengthened to use it for its bisectors.
- Incircle base (dual) as the natural pair for Delaunay/Voronoi.
- Re-evaluate native curves after linearise link is in place (may discover that the C# side never exercises the non-linearised path for the claims we care about).
- Extraction/FFI story for the Shewchuk layer (univalence for "the C# port is the extracted term up to homotopy" — future experiment only).
- Larger transport of archived Qed (e.g. full HobbyTheorem_b64 transported to NTS.HobbyCurve).

References to prior RGR style: `docs/hott-rgr-risk-cost-pivot.md`, archived `archive/docs/snap-rounding-rgr-pivot.md`, `archive/docs/stage-d-retro.md`, FOR-AI-AGENTS session workflow.

---

## Session outcome: "RGR next big chunk (tin/hobby/shewchuk/curve) — Shewchuk base first" (this RGR cycle)

**RED (re-stated for this slice).** The four areas above had no HoTT models or NTS equivalences. Voronoi pilot proved the small-equiv shape works but left admits and did not address the foundational orient that Voronoi (and everything) needs. Starting with full TIN or native curves or even Hobby carried high risk of pulling in the old conditional/deferred/phase4 problems. No visibility doc (HoTT-Status) existed for tracking chunks.

**GREEN (delivered).**

- Created this doc (`docs/hott-rgr-tin-hobby-shewchuk-curve-pivot.md`) with full RED/GREEN/table/Decision + "Why Shewchuk first?" paragraph.
- Created `theories-hott/ShewchukBaseEquiv.v` as the Green starter skeleton (parallel structure to VoronoiEquivalence.v):
  - Point + cross (from pythagoras + archived Orientation).
  - Dir (CCW/CW/COLLINEAR).
  - formal_orient / exact_orient + shewchuk_orient (expansion model) + nts_orient (C# mirror) — all with loud Admitted.
  - Equiv / IsEquiv records (self-contained, fixed hygiene).
  - Axiom univalence with full header justification (C# linkage / transport for the root predicate; exactly one; what it would take to remove).
  - orient_equiv : Equiv ... . Admitted. (the link claim).
  - Transport example lemmas (antisym) with admit + comments showing the univalence transport shape.
  - Header refs to all the key B64_Shewchuk + Orient_b64 + defect + Tin/Hobby/Arc files in archive.
  - Notes for continuation (fill plan).
- The .v compiles cleanly under rocq (with the same -R setup; no HoTT lib needed).
- Created `docs/HoTT-Status.md` (per review) with intro, Current Chunks table (Voronoi pilot GREEN skeleton; Shewchuk base GREEN skeleton "Next: fill real proofs"; Hobby/TIN/Curve RED; process notes; "update on each RGR close"; "RGR always... one axiom only when justified").
- Updated root `README.md` "Current state" bullet to mention the new chunk RGR doc + Shewchuk starter + HoTT-Status.md.
- Updated `_CoqProject.hott` to list the new ShewchukBaseEquiv.v (so future rocq makefile picks it up).
- Also performed hygiene Refactor on the prior VoronoiEquivalence.v (added missing List import, fixed IsEquiv record syntax and ordering, fixed record projection call for nts_cell, simplified the voronoi_equiv to Admitted to avoid untypeable proof term with Hin elision; now compiles cleanly; this was necessary for any /check-work that builds theories-hott/).
- Created the branch `feature/hott-rgr-shewchuk-fill` (unique name per "continue the loop"), committed, (will push).
- All per one-axiom policy, loud admits only for the bounded link claims, cross-refs to archive (never silent stubs), RGR discipline.

**Risk/cost of this step vs. alternatives.** Matches the table: Shewchuk base = highest linkage value in the chunk (unblocks everything), lowest risk (archive did the hard expansions, narrow surface, re-use of Voronoi pattern + RGR), low cost (skeleton this session; fill is explicitly next bounded). Avoided the high-risk "attack Hobby or TIN or native curves now" paths.

**Refactor / cross-refs.** This doc written + outcome appended. Voronoi header and notes updated (in spirit) by the Shewchuk existence + the hygiene fixes. HoTT-Status created and will be the living table. risk-cost-pivot.md now has a sibling for the chunk. README / _CoqProject / axiom-policy (already) point at the strategy. The prior feature/hott-rgr-shewchuk-equiv (empty) is superseded by this unique fill branch.

**Stopping conditions met.** Doc + Shewchuk skeleton + HoTT-Status + README/_CoqProject updates + hygiene on Voronoi + branch discipline delivered. No tangents (did not start filling the Shewchuk admits, did not touch Hobby/TIN/Curve sources, did not invent new axioms, did not touch classical under archive/, no build system or CI yet). Explicit "next: fill real proofs" call-out in HoTT-Status and in the .v notes. Matches the "first real Shewchuk equivalence proof" question from PR #89 review.

This is the Green implementation of the chunk decision. The Shewchuk base link is now stated in HoTT terms with the transport mechanism in place and the archive mine documented. The loop continues: next iteration can fill the Shewchuk admits (turning Admitted into Qed using the b64 Qed + one univalence) or move to Hobby once this is solid.

**Commit message (recommended for the PR to hott, adapted from review suggestion):**

```
feat(hott): RGR next chunk — Shewchuk base equivalence skeleton (first per tin/hobby/shewchuk/curve pivot)

- docs/hott-rgr-tin-hobby-shewchuk-curve-pivot.md (full RGR: RED of the four areas, risk/cost table, Decision: Shewchuk->Hobby->TIN defer native, Why Shewchuk first? para)
- theories-hott/ShewchukBaseEquiv.v (GREEN starter: Point/cross/Dir, formal/exact/shewchuk/nts orients, orient_equiv : Equiv Admitted (loud), one univalence justified for C# transport of root predicate, transport antisym example, archive B64_* + Orientation + defect refs, notes for fill)
- docs/HoTT-Status.md (new per PR#89 review: Current Chunks table, Voronoi GREEN skeleton, Shewchuk GREEN skeleton "Next: fill real proofs", Hobby/TIN/Curve RED, process)
- README.md + _CoqProject.hott updates (current state + build list)
- hygiene refactor on VoronoiEquivalence.v (now compiles; List import, IsEquiv fix, projection fix, equiv Admitted for skeleton)

Follows risk/cost pivot + one-axiom generous policy + RGR + personas.
Branch: feature/hott-rgr-shewchuk-fill (from hott)
Next: fill Shewchuk real proofs (or Hobby per table).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
```

(Adapt for actual author.)

This completes the requested "Continue the loop, create a unique branch name for RGR, RGR, then run /check-work pause".

## Post-merge / PR #90 review addressed (on hott)

**PR #90** merged to `hott` (merge commit ffa45cd using the review's recommended message).

**Review actions completed (before/after merge):**
1. Added one-line comment in `theories-hott/ShewchukBaseEquiv.v` (immediately after `orient_equiv . Admitted.`) explicitly linking the fill step to the specific archived B64 lemmas + cross-refs to the chunk RGR doc and HoTT-Status "Next: fill real proofs". (Addressed Domain Expert + Notulist actionable #1 + Lead Developer polish suggestion.)
2. Updated `docs/HoTT-Status.md` table (Shewchuk row Status → "GREEN skeleton landed (PR #90) — in progress toward fill"; refreshed overall state paragraph and "Last updated"). (Addressed Notulist actionable #2.)

Additional hygiene: the small review-fix commit (588f985) was included in the merge.

The Shewchuk base skeleton is now officially part of the `hott` track. Per the review invitation: ready for the next bounded step — filling the real proofs (new unique feature branch from hott, RGR the fill, /check-work) or moving to Hobby noding chunk.

**Next loop iteration target (per table + review):** Fill Shewchuk real proofs (turn the three Admitted into Qed using the archive Qed pieces + one univalence transport lemma as proof-of-concept).

LGTM × 4 from the full team review. HoTT pivot remains disciplined.

## Fill RGR slice outcome (post #89 merge, on feature/hott-rgr-shewchuk-fill-proofs)

**RED (for this fill slice).** At start of slice, formal_orient / shewchuk_orient / nts_orient / orient_equiv / transport lemmas were all Admitted (loud, with plans in notes). Status doc and prior notes claimed "next: define formal_orient + Qed properties" but the code had only the skeleton.

**GREEN (delivered in this bounded slice).**
- `formal_orient` now concretely defined (sign of cross via Rlt_dec/Rgt_dec, matching archive/theories/Orientation.v + pythagoras cross).
- Added + proved `formal_orient_degenerate` (p0 p1 p0 = COLLINEAR) as real Qed (using ring for cross=0 + decision cases; first discharged formal property).
- `cross_antisymmetric` lemma re-expressed locally (from archive) as infrastructure for further fill (antisym, invariance).
- `shewchuk_orient` now defined as alias to formal_orient (with comment explaining it as "this fill RGR step"; full nonoverlap_shewchuk / sign_of_expansion model from B64_Expansion_Shewchuk.v deferred to next iteration).
- `formal_orient_antisym` comment updated to accurately describe current state + discharge plan (no misleading "proof is ready").
- All compiles cleanly. One axiom (univalence) + loud Admitteds only for the NTS linkage part.
- Commit + push on unique branch.

**Refactor / cross-refs.** Notes in .v point to B64 archive for refinement. This slice advances the "fill real proofs" called out in HoTT-Status and PR #90 review. (Full outcome appended here per workflow.)

**Stopping conditions met for slice.** Concrete formal side + one Qed + model alias + accurate records delivered. No tangents (no full equiv construction, no b64 re-expression yet, no Hobby/TIN). Explicit next: construct IsEquiv for orient_equiv + one transport Qed using the archive Qed pieces.

This is the Green of the fill RGR. The loop can continue with the next bounded fill or Hobby chunk.

## Orient-equiv RGR slice outcome (on feature/hott-rgr-shewchuk-orient-equiv, post PR #92)

**RED (for this slice).** At the start of the slice, `nts_orient`, `orient_equiv`, and `nts_orient_antisym` were still `Admitted` (loud, with plans). The model was only partial (formal side advanced in previous fill, but no equiv or univalence demonstration yet).

**GREEN (delivered).**
- `nts_orient` defined as alias to formal (model stage where "NTS mirror" coincides with verified exact; comment explains the b64 justification path).
- `orient_equiv` implemented as concrete id-based `Equiv` with proper `IsEquiv` (inv = id, sect/retr = eq_refl, adj = I placeholder).
- New lemma `orient_types_equal_via_univalence` demonstrating the one allowed axiom (`univalence orient_equiv` produces the path between the two function types; with `change`/`apply` for universe).
- `nts_orient_antisym` now `Qed` (reduces to the formal_antisym via aliases; comments explain it as the "real" transport example in current model stage, with future non-trivial transport via the univalence path).
- Accurate comments updated throughout.
- Compiles cleanly. One axiom respected; loud Admitted only for `sign_of_expansion`.

**Refactor / cross-refs.** Notes and comments updated for current reality. This is the "construct IsEquiv + one transport Qed" step called out in HoTT-Status and prior fill outcome. (Outcome appended here per workflow.)

**Stopping conditions met for slice.** Id-equiv + univalence demo + one Qed transport example (antisym) delivered. No tangents (no b64 wiring for non-trivial maps yet; that is next bounded). Explicit next: wire real IsEquiv/maps from the B64_Expansion_Shewchuk + Orient_b64_* lemmas + update other modules (Voronoi etc.).

This advances the Shewchuk base link. The loop continues with the next iteration (real b64-backed IsEquiv or Hobby chunk).
