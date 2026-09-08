# Reading guide — who reads what

The corpus's docs cover several actors with different reading needs.
This index maps each actor to their starting point and recommended
path through the docs.

Names are mnemonic — they alliterate with the role so they stick.

---

## 🌍 GIS Gus

**Role.** Uses NetTopologySuite for spatial computation; curious about
which geometric primitives have formal proofs.

**Start at.** [`README.md`](../README.md), then in order:

  1. [`phase0-completion.md`](phase0-completion.md) — orient2d (Shewchuk Stage A robust
     orientation).
  2. [`phase1-completion.md`](phase1-completion.md) — segment-pair intersection (filtered +
     exact + forward-error).
  3. [`phase2-hotpixel-progress.md`](phase2-hotpixel-progress.md) — hot-pixel snap-rounding (the
     Phase 2 milestone progression).
  4. [`audit-phase3-overlay.md`](audit-phase3-overlay.md) § headers — polygon overlay correctness
     (Union/Intersection/Difference/SymDiff).
  5. [`audit-phase4-curves.md`](audit-phase4-curves.md) § headers — arc/curve overlay status
     (SQL/MM ISO/IEC 13249-3 CIRCULARSTRING / COMPOUNDCURVE /
     CURVEPOLYGON; `arc_overlay_correct_chord_approx` is the
     named-hypothesis / chord-approx claim, JCT gap precisely
     characterised).

For the citable index of every Qed-closed theorem (with axiom footprint
and regime), see [`verified-claims.md`](verified-claims.md).

**Skip.** Anything under [`docs/history/sessions/`](history/sessions/) (forensic), the
Shewchuk Theorem 13 deep-dives (research-grade), and the Hobby-lemma
docs (cell-snap-rounding internals).

**Take away.** The corpus has Qed-closed soundness for orient2d,
intersection, snap-rounding's preservation invariant, a conditional
headline for polygon overlay (`overlay_ng_correct_conditional`), and
named-hypothesis / chord-approx curve overlay (`arc_overlay_correct_chord_approx`).
Gaps are precisely named, not handwaved.

---

## 🏗️ BIM Bea

**Role.** Models as-built geometry; cares about CIRCULARSTRING /
COMPOUNDCURVE / CURVEPOLYGON (SQL/MM ISO/IEC 13249-3). NTS `Flatten()`
linearizes those curves to chords before overlay — Flatten is lossy
and is not the curve.

**Start at.** [`audit-phase4-curves.md`](audit-phase4-curves.md), then:

  1. [`audit-phase4-chord-overfitting.md`](audit-phase4-chord-overfitting.md) — the chord-approximation
     thesis direction (Option B).
  2. [`point-in-ring-jct-path.md`](point-in-ring-jct-path.md) — JCT path to `point_in_ring_correct`
     (relevant for ring-membership in valid polygons with arcs).
  3. [`theories/ArcOrient.v`](../theories/ArcOrient.v), [`theories/ArcIntersect.v`](../theories/ArcIntersect.v),
     [`theories/ArcHotPixel.v`](../theories/ArcHotPixel.v) file headers — the R-side arc
     predicates.
  4. `theories-flocq/ArcOrient_b64.v`,
     `theories-flocq/ArcIntersect_b64.v`,
     `theories-flocq/ArcHotPixel_b64.v` file headers — the binary64
     mirrors. (NB: the live b64 arc files are
     [`theories-flocq/ArcCircle_b64_compute.v`](../theories-flocq/ArcCircle_b64_compute.v) and
     [`theories-flocq/ArcPixel_b64_compute.v`](../theories-flocq/ArcPixel_b64_compute.v); the three names
     above are stale.)

The curve-awareness proof needs and their status across issues #64–#69
are triaged in [`../TRIAGE_NTS_JTS_ISSUES.md`](../TRIAGE_NTS_JTS_ISSUES.md) (umbrella) and the
per-area [`issue-64-arc-primitives-triage.md`](issue-64-arc-primitives-triage.md); the clothoid
lane's open questions in [`clothoid-open-questions-triage.md`](clothoid-open-questions-triage.md).

**Skip.** Phase 0/1/2 unless you care about the underlying primitives.

**Take away.** Arc-overlay correctness is the named-hypothesis / chord-approx claim
(`arc_overlay_correct_chord_approx`); the b64 in-circle layer now has
Qed-closed sign + integer-regime value exactness
([`theories-flocq/InCircle_b64_exact.v`](../theories-flocq/InCircle_b64_exact.v),
Flocq-free Z/R kernel in
[`InCircle_b64_exact_refs.v`](../theories-flocq/InCircle_b64_exact_refs.v);
PR #146). Arc-line coordinates are Scope A only ([`theories-flocq/ArcLineIntersect_b64_exact.v`](../theories-flocq/ArcLineIntersect_b64_exact.v)
— `sP`/`sQ`/`dx`/`dy` before division).

**Trust chain.** The Phase 4 oracle modes (INCIRCLE_SIGN,
ARC_CHORD_CROSSES_CIRCLE, ARC_PASSES_THROUGH_PIXEL) extract directly
from the Coq layer — they are no longer hand-rolled OCaml. INCIRCLE_SIGN
is backed by `b64_inCircle_B2R_sign_sound_small_int` at `|coord| <= 2^11`
(degree-4 chain; tighter than orient2d's `2^25`). When a mode says
TRUE/FALSE, the Coq theorem behind it is identifiable from the protocol
docstring in [`oracle/driver.ml`](../oracle/driver.ml) and [`verified-claims.md`](verified-claims.md).

---

## 🛠️ Quality Gatekeeper (Max/Ruby)

**Role.** Keeps CI green, merges PRs, manages the deferred-proof
registry, owns the build pipeline details, and reviews PRs for
correctness and adherence to corpus discipline.

**Start at.** The four CI-enforced registries:

  1. [`axiom-allowlist.txt`](axiom-allowlist.txt) — the three permitted axioms.
  2. [`audit-exceptions.txt`](audit-exceptions.txt) — Category C per-file Classical_Prop pull
     exemptions.
  3. [`admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt) — registered Admitteds with
     discharge plans.
  4. [`admitted-counterexamples.txt`](admitted-counterexamples.txt) — registered Admitteds with
     verified-false statements.

**Also.** [`.github/workflows/ci.yml`](../.github/workflows/ci.yml) +
[`build-oracle.yml`](../.github/workflows/build-oracle.yml), the [`Dockerfile`](../Dockerfile), [`docs/development-environment.md`](development-environment.md).
The living theorem index is [`verified-claims.md`](verified-claims.md), checked by
[`scripts/validate-claims.sh`](../scripts/validate-claims.sh) on every CI run.

**On every PR.** Run [`scripts/check_admitted.sh`](../scripts/check_admitted.sh),
[`scripts/audit_axioms.sh`](../scripts/audit_axioms.sh), [`scripts/check_readme_axioms.sh`](../scripts/check_readme_axioms.sh) — they're
the per-PR sanity net.

**Reject.** Bare `Admitted.` without registry entry, hand-rolled OCaml
when an extracted version exists, or wrappers with no new content.

**Skip.** Per-session forensic traces unless investigating a specific
Admitted's lineage.

**Take away.** The corpus's epistemic invariants are machine-checkable;
the gatekeeper's job is to keep the registries and pipeline in sync
with the `.v` files and review PRs against them. (CI Cara and Risk-Officer Rico responsibilities now live under this combined Quality Gatekeeper role.)

**When a new Admitted lands.** Add an entry to
[`admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt) (provable) or
[`admitted-counterexamples.txt`](admitted-counterexamples.txt) (counterexample-blocked) with the
format:
`file:theorem_name | proof_structure_doc | section_references`.
The entry should include a discharge plan + consumer chain (which
downstream theorems use it). [`scripts/check_admitted.sh`](../scripts/check_admitted.sh) validates
the registration on every CI run.

---

## 🎓 Scholar Sam (incl. Auditor Avery)

**Role.** Researches formal methods / mechanised geometry; evaluates
the corpus's methodology (including independent formal-methods audits
and trust-chain verification).

**Start at.** [`slice-a-retro.md`](slice-a-retro.md) and [`slice-a-piece-5b-retro.md`](slice-a-piece-5b-retro.md) —
engagement-level syntheses.

**Then in any order:**

  1. [`audit-phase2-snap-rounding.md`](audit-phase2-snap-rounding.md), [`audit-phase3-overlay.md`](audit-phase3-overlay.md),
     [`audit-phase3-milestone5.md`](audit-phase3-milestone5.md), [`audit-phase4-curves.md`](audit-phase4-curves.md),
     [`audit-shewchuk-stages.md`](audit-shewchuk-stages.md) — per-phase proof-structure audits.
  2. [`hobby-theorem-proof-structure.md`](hobby-theorem-proof-structure.md),
     [`shewchuk-theorem-13-proof-structure.md`](shewchuk-theorem-13-proof-structure.md) — proof structures for
     the named load-bearing theorems.
  3. [`point-in-ring-seams-3-5-7-red.md`](point-in-ring-seams-3-5-7-red.md) (or [`point-in-ring-jct-path.md`](point-in-ring-jct-path.md)),
     [`point-in-ring-seam-attempts.md`](point-in-ring-seam-attempts.md),
     [`point-in-ring-tangent-attempts.md`](point-in-ring-tangent-attempts.md) — the JCT / seven-seam analysis
     of `point_in_ring_correct` (Phase 5 work).
  4. [`soundness-strategy.md`](soundness-strategy.md), [`stage-d-feasibility.md`](stage-d-feasibility.md),
     [`stage-d-retro.md`](stage-d-retro.md), [`stage-d-chain-composition-approach.md`](stage-d-chain-composition-approach.md) —
     soundness-strategy retrospectives.
  5. [`docs/history/sessions/`](history/sessions/) — per-session forensic record (only
     when you need to verify the chronology or read precise stuck
     goals).
  6. The four registries + run `scripts/audit_axioms.sh /tmp/full-build.log`
     (for trust-chain / axiom footprint audits).
  7. [`library-footnotes.md`](library-footnotes.md) — the operator paper
     library mapped against the corpus: which papers have an honest
     descendant (header cite + DOI + paper-CLAIMS vs file-PROVES), which
     have no module to sit under yet and their suggested future home, and
     the misnomers recorded but deliberately not rewritten in-tree.

**Take away.** Two patterns to watch: the **conditional headline**
(Qed-closed theorem under named thesis-shaped hypotheses) and the
**deferred-proof registry** (Admitted with documented discharge
plan). Both make load-bearing gaps precise.

**Methodology meta-pattern.** Two current headlines instantiate
the conditional pattern (`hobby_theorem_4_1_conditional`,
`overlay_ng_correct_conditional`). Each is Qed-closed under named
thesis-shaped hypotheses; the corpus's contribution is the
structural composition plus the precise naming of the load-bearing
gaps, not the discharge of those gaps. `arc_overlay_correct_chord_approx`
is the named-hypothesis / chord-approx claim. `point_in_ring_correct_jct` is the vacuous
stdlib shell, not a current conditional headline. This pattern is the
corpus's shipping discipline; cite as such.

**Tiers (when auditing).** Forbidden / counterexample / deferred-proof.

---

## 📋 Project Meta (Pat/Sara)

**Role.** Decides what ships next, tracks phase completion, budgets
sessions, plans cadence, and retrospects on how the work actually went.

**Start at.** Top-level retros + [`phase0-completion.md`](phase0-completion.md),
[`phase1-completion.md`](phase1-completion.md), [`phase2-hotpixel-progress.md`](phase2-hotpixel-progress.md) — what's done.

**Then for "what's next" and cadence:**

  1. [`ecosystem-search-2026-05-29.md`](ecosystem-search-2026-05-29.md) — JCT / Real.structure / atan2
     ecosystem audit; verdicts with cost estimates.
  2. [`point-in-ring-seams-3-5-7-red.md`](point-in-ring-seams-3-5-7-red.md) — most recent gap inventory
     for `point_in_ring_correct` with cost-per-seam.
  3. [`admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt) — every registered Admitted has
     a discharge plan + consumer chain; this is the next-work
     backlog.
  4. [`docs/history/sessions/README.md`](history/sessions/README.md) — index of per-session
     prompts + outcomes (chronological).
  5. [`../TRIAGE_NTS_JTS_ISSUES.md`](../TRIAGE_NTS_JTS_ISSUES.md) — the curve-awareness proof
     batch (#64–#69) triage + order of attack; per-area detail in
     [`issue-64-arc-primitives-triage.md`](issue-64-arc-primitives-triage.md),
     [`relate-ng-status.md`](relate-ng-status.md) (living; archive:
     [`history/issue-67-relateng-triage.md`](history/issue-67-relateng-triage.md)),
     and
     [`clothoid-open-questions-triage.md`](clothoid-open-questions-triage.md).

**Skip.** (Nothing major — this combined role owns the meta layer.)

**Take away.** The conditional-headline pattern means "what's the
next thesis-scale gap to discharge or the next library to import" is
the right next-work granularity. Don't budget for ad-hoc work; budget
for one registry entry at a time.

**Session sizing rule of thumb.** A session typically lands 1-3
Qed-closed deliverables; ~10% collapse outright (documented as
collapse artifacts). Multi-session engagements (Slice A Piece 5b
Route 1 ran 17 sessions; Phase 1 C.2-tight ran 6) close one
deferred-proof registry entry. When scoping a new entry, multiply
the estimated session count by 1.5x for unknown unknowns.

**Session structure template.** Prompts follow a five-phase shape:
  - **Grep first**: gather corpus state before writing.
  - **Red phase**: state the simplest target lemma + predicted
    tangents in order of likelihood.
  - **Green phase**: deliverables in order, stop at first genuine
    tangent.
  - **Refactor phase**: gauntlet (`check_admitted`, `audit_axioms`,
    `check_readme_axioms`).
  - **Stopping conditions**: explicit full-success and tangent-stop
    criteria.
Use this template when proposing new sessions. The discipline of
stating stopping conditions up front prevents scope creep mid-session.

---

## 🌱 Newbie Nate (incl. Plain Reader Pete / 🧮 Rocq Rookie Ray)

**Role.** First contribution to the corpus; or casual reader who picked up the repo from a link and wants the elevator pitch; or absolute beginner with zero prior exposure to proof assistants (Rocq/Coq).

**Start at.** `make help` + [`pythagoras-for-beginners.v`](pythagoras-for-beginners.v) (the 60-second / zero-prior path). The [`README.md`](../README.md) first screen is the elevator. Long-form invariant: [The invariant](#the-invariant) below.

(If you have literally never seen a proof assistant before: open [`docs/pythagoras-for-beginners.v`](pythagoras-for-beginners.v) in an IDE (CoqIDE / VSCode + VSCoq) and step through it. It is deliberately self-contained, starts from `Record Point`, defines `dist_sq`, proves the 3-4-5 case first with `ring` then explicitly with asserts/rewrites for pedagogy, and pre-bunks "why spend so much compute on obvious geometry?": even Pythagoras is non-trivial once every algebraic step must be justified from the axioms; the load-bearing chokepoints like orientation/intersection/snap-rounding are what justify the engineering investment.)

A second gentle on-ramp is [`docs/sqrt3-irrational-for-beginners.v`](sqrt3-irrational-for-beginners.v).  It proves the classical fact that `sqrt 3` is irrational by Fermat-style infinite descent over the integers, then lifts the result to the reals.  The file contains an unusually explicit "honesty note" explaining that this number-theoretic fact is *not* used by the geometric work in the corpus (the hex embeddings keep `sqrt 3` explicitly and discharge the necessary arithmetic with `lra`/`nra`/`field`).  It is included purely as a teaching example of descent and of moving between `Z` and `R`.

**Then (for contributors / deeper dive):**

  1. [`development-environment.md`](development-environment.md) — get the toolchain running.
  2. Any one Phase completion doc that touches your area of interest.
  3. The corresponding `audit-*.md` for that phase.
  4. A short Qed-closed file (e.g. [`theories/ArcIntersect.v`](../theories/ArcIntersect.v), ~200
     lines) — read end-to-end as a sample.

**For your first PR.**
  - Pick the smallest Admitted in [`admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt)
    whose discharge plan you understand.
  - Or pick a `WHAT IS QED-CLOSED / WHAT REMAINS OPEN` item from
    one of the audits.

**Skip.** The Slice A piece 5b cascade-invariant work — it's deep and
non-onboarding-friendly.

**Take away.** The bar is high but the discipline is documented.
Read one full PR (e.g. the recent Phase 4 Session A) to see the
shape.

**Where to ask questions.** Open a GitHub Issue on this repo for
substantive questions; for "is this PR ready?" drop a comment on
the PR. Review cadence is typically same-day for PR triage, 1-3
days for full review.

---

## 🧑‍🔧 Tech-Lead Tess

**Role.** Designs new engagements, sequences sessions, decides
scope.

**Start at.** The retros (Scrum-Master Sara's path) + the
proof-structure docs (Scholar Sam's path).

**Then:**

  1. The `stage-d-*.md` cluster — design-route documentation for
     Stage D (a complex multi-route engagement):
     [`stage-d-feasibility.md`](stage-d-feasibility.md), [`stage-d-retro.md`](stage-d-retro.md),
     [`stage-d-chain-composition-approach.md`](stage-d-chain-composition-approach.md).
  2. [`docs/history/sessions/slice-a-piece-5b-route1-design-session.md`](history/sessions/slice-a-piece-5b-route1-design-session.md)
     — what a design-session artifact looks like.
  3. [`point-in-ring-seams-3-5-7-red.md`](point-in-ring-seams-3-5-7-red.md) (or [`point-in-ring-jct-path.md`](point-in-ring-jct-path.md)) — exemplar seam-map / JCT path work
     workflow for breaking down a thesis-scale problem.
  4. [`audit-phase3-milestone5.md`](audit-phase3-milestone5.md) § 6 (Conditional strategy) — how
     the conditional-headline decision was made.

**Take away.** Design sessions produce mermaid diagrams + named-
hypothesis decompositions; implementation sessions discharge or
defer them. Two-route design (when uncertain) is documented as a
methodology.

**Methodology patterns to lean on.**
  - **Two-route design**: when the load-bearing approach is
    uncertain, design both routes in parallel. One typically
    collapses (e.g. Slice A Piece 5b Route 2 collapsed at Session
    2); the surviving route inherits the design insights.
  - **Seam map**: when a target theorem decomposes into N
    sub-problems, write each as a "seam" with what-exists / what's-
    missing / cost-per-seam. See
    [`point-in-ring-seams-3-5-7-red.md`](point-in-ring-seams-3-5-7-red.md) (or [`point-in-ring-jct-path.md`](point-in-ring-jct-path.md)) as the exemplar.
  - **Red/green workflow**: red = state simplest target + predicted
    tangents; green = attempt each, stop at first genuine tangent.
    The recent [`point-in-ring-seams-3-5-7-red.md`](point-in-ring-seams-3-5-7-red.md) +
    [`point-in-ring-tangent-attempts.md`](point-in-ring-tangent-attempts.md) pair shows the cadence.

---

## 📦 Consumer Connie

**Role.** Downstream consumer (e.g. `.Curve` C# differential-test
runner, oracle binary user).

**Start at.** [`README.md`](../README.md) + [`oracle/driver.ml`](../oracle/driver.ml) head docstring (the
protocol reference).

**Then:**

  1. The [`oracle/driver.ml`](../oracle/driver.ml) file header — protocol
     reference for the documented modes (about 26). Dispatch is larger
     (about 60). `HOLE_*` is help+dispatch only (not a header protocol
     entry). `INCIRCLE_SIGN` / `ARC_CHORD_CROSSES_CIRCLE` are extracted
     (MIGRATED), not HAND-ROLLED. `PASSES_THROUGH_*` dispatch is
     `*_compute`, not the R-spec names.
  2. [`.github/workflows/build-oracle.yml`](../.github/workflows/build-oracle.yml) — how `oracle_bin` is
     built and published.
  3. The Phase 4 audit + recent `Arc*_b64.v` headers for the trust
     chain of the Phase 4 modes; each mode's backing theorem is in
     [`verified-claims.md`](verified-claims.md).

**Skip.** Internal Coq proof structures — you trust the Qed.

**Take away.** Each oracle mode either extracts directly from a
Coq-verified function or is hand-rolled with an explicit Coq pin
comment. Phase 4 modes recently swapped from hand-rolled to
extracted (commit `bd6d01f` on `claude/oracle-arc-extracted`).

**JTS ↔ NTS RocqRefRunner port (catalyst).** The integer-domain
reference both languages implement is proved in
[`theories/RocqRefRunner.v`](../theories/RocqRefRunner.v)
(`rocqref_refSign_eq_cross`, `rocqref_idet_fits_int64`). Shared
vectors: [`oracle/rocqref/jts_nts_equiv_vectors.txt`](../oracle/rocqref/jts_nts_equiv_vectors.txt).
Write-up: [`rocqref-jts-nts-equiv.md`](rocqref-jts-nts-equiv.md).
This is **not** a soundness proof of production `Orientation.index`.

**Differential test pattern.** The intended consumer workflow:
keep one long-running `oracle_bin` instance; the C# differential
runner sends a mode line + inputs over stdin; the binary replies
on stdout in hex-float format ("%h") so consumers can round-trip
bits exactly. Persistent-mode dispatch is the design (every mode
except SIMPLIFY loops back). See Phase 0 `.Curve` C# port for the
reference implementation.

**In-process alternative (Phase 5).** For call sites where a
subprocess per predicate is not viable — a noding loop, not a test
corpus — the same extracted kernel is also a C ABI: `libntsrocq`
([`oracle/nts_ffi.h`](../oracle/nts_ffi.h)), bound from .NET by
[`oracle/csharp/RocqNative.cs`](../oracle/csharp/RocqNative.cs) and
held bit-identical to the `oracle_bin` protocol by
[`oracle/gen_ffi_parity_tests.py`](../oracle/gen_ffi_parity_tests.py).
Read [`phase5-ffi-abi.md`](phase5-ffi-abi.md) first — §4 is the
per-entry-point soundness ledger, including which predicates are
sufficient-only and which have an exact in-process fallback (orientation
does: `nts_rocq_orient_sign_exact`; in-circle / passes-through do not yet).

---

## 🧭 NTS-Upstream Norm

**Role.** Writes NetTopologySuite code upstream; needs to know which
algorithms have proofs and what those proofs imply for behaviour.

**Start at.** [The invariant](#the-invariant) + the four phase-
completion docs ([`phase0-completion.md`](phase0-completion.md), [`phase1-completion.md`](phase1-completion.md),
[`phase2-hotpixel-progress.md`](phase2-hotpixel-progress.md), [`audit-phase3-overlay.md`](audit-phase3-overlay.md)).

**Then:**

  1. Map each NTS algorithm to its corpus counterpart (theorem
     statements indexed in [`verified-claims.md`](verified-claims.md)):
     - `RobustLineIntersector` → `b64_intersect_*` (Phase 0/1).
     - `RobustDeterminant` → `b64_orient2d` + Stage A filter (Phase 0).
     - `HotPixel` snap-rounding → `b64_in_hot_pixel` + snap-round
       preservation (Phase 2; Flocq-free R-side kernel in
       [`HotPixel_b64_refs.v`](../theories-flocq/HotPixel_b64_refs.v)).
     - `OverlayNG` boolean ops → `overlay_ng_correct_conditional`
       (Phase 3, conditional).
     - CIRCULARSTRING arc operations → Phase 4 `Arc*_b64.v` +
       [`InCircle_b64_exact.v`](../theories-flocq/InCircle_b64_exact.v) / [`ArcLineIntersect_b64_exact.v`](../theories-flocq/ArcLineIntersect_b64_exact.v)
       (in-circle exact at `|coord| <= 2^11`; arc-line Scope A).
     - RelateNG / DE-9IM predicates → [`theories/DE9IM.v`](../theories/DE9IM.v),
       [`theories/RelateLineLine.v`](../theories/RelateLineLine.v), [`theories/RelateIntDetBound.v`](../theories/RelateIntDetBound.v)
       (#67 living status: [`relate-ng-status.md`](relate-ng-status.md);
       #522 wrap-up: [`scout/522-closing-summary.md`](scout/522-closing-summary.md)
       and [`scout/map-522.md`](scout/map-522.md)).
  2. Read the soundness theorem statement (not its proof) for the
     algorithm you're touching.

**Skip.** Coq proof internals. Read the file header's `WHAT THIS
FILE LANDS` block as the spec.

**Take away.** Proofs apply to the corpus's binary64 mirrors of NTS
algorithms. Bit-exact agreement holds on int-safe inputs (e.g.
|coord| <= 2^25 for orient2d, |coord| <= 2^11 for inCircle_R); on
mixed inputs, the filtered predicates give a sound 4-way
classification (POS / NEG / ZERO / UNCERTAIN) and callers must
fall back when UNCERTAIN — for orientation that fallback is now
in-process (`nts_rocq_orient_sign_exact`, exact over all finite
doubles).

---

## 🧠 Joost the BDFL (Joost mag het weten)

**Role.** The benevolent dictator for life of the corpus — not the product owner. "Joost mag het weten" is the Dutch proverb ("only Joost knows" / "Joost may know it all"). He is assumed to have (or be able to quickly form) the complete picture of the corpus, its history, its gaps, and its long-term shape. Jeroen is the product owner of scope and priority.

**Start at.** The [`README.md`](../README.md) first screen, the complete [`READING-GUIDE.md`](READING-GUIDE.md) (including the [long-form corpus notes](#long-form-corpus-notes-off-the-readme-first-screen)), every major retro and proof-structure document, the entire [`docs/history/`](history/) tree (especially [`sessions/`](history/sessions/)), the strategy and seam-map documents, and the CI/oracle credibility material. You are the one actor whose path legitimately exercises the archive.

**Special power.** BDFL final say on:
- Whether a marginal file stays at top level or moves to history/.
- Tie-breakers when the strict "useful for one of the other defined actors" rule is in conflict with institutional memory or future utility.
- Architecture and "what the project is" questions (corpus identity, not PI priority).

Jeroen owns product scope and priority. Joost does not own the JTS curve backlog or PI priority.

In pruning work, Joost is the explicit exception to the actor filter and the person who reviews the stop-condition batch results.

**Take away.** You know (or can find out) why every artifact exists and where it lives. Your job includes making sure the other actors have the right on-ramps and that nothing important is lost in the archive.

---

## 🎯 Summary table

| Mnemonic | Role | First doc | Reading time |
|---|---|---|---|
| Newbie Nate (incl. Plain Reader Pete / Rocq Rookie Ray) | Casual reader / first contrib / zero-knowledge Coq on-ramp via pythagoras + sqrt3 example | `make help` + [`pythagoras-for-beginners.v`](pythagoras-for-beginners.v) + [`sqrt3-irrational-for-beginners.v`](sqrt3-irrational-for-beginners.v) | 1-10 min + examples |
| GIS Gus             | GIS user                    | [`README.md`](../README.md) → `phase[0-2]-*.md` → [`audit-phase3-overlay.md`](audit-phase3-overlay.md) → [`audit-phase4-curves.md`](audit-phase4-curves.md) | 30 min |
| BIM Bea             | BIM user                    | [`audit-phase4-curves.md`](audit-phase4-curves.md)               | 1 h |
| Quality Gatekeeper (Max/Ruby) | Corpus maintainer + PR reviewer + CI/Risk | [`axiom-allowlist.txt`](axiom-allowlist.txt) + registries + [`ci.yml`](../.github/workflows/ci.yml) | 20 min |
| Scholar Sam (incl. Auditor) | Formal-methods researcher + independent audit | [`slice-a-retro.md`](slice-a-retro.md) + registries + audit script | half day |
| Project Meta (Pat/Sara) | Roadmap / scope + session cadence | [`phase*-completion.md`](phase0-completion.md) + top-level retros + [`history/sessions/`](history/sessions/) | 1-2 h |
| Tech-Lead Tess      | Engagement design           | retros + proof-structure docs / seam maps | half day |
| Consumer Connie / NTS-Upstream Norm | Oracle binary user or NTS upstream contributor | [`oracle/driver.ml`](../oracle/driver.ml) header + phase completions | 15-60 min |
| Joost the BDFL      | Benevolent dictator for life (Joost mag het weten) | Full README + READING-GUIDE + entire history/ tree | as needed |

(Note: several roles were collapsed for overlap after the initial 17-card list (17→10): Pat/Sara, Max/Ruby, Auditor into Scholar, CI/Risk into Quality, Pete into Nate/Ray. Folded roles stay named on surviving cards. Consumer Connie and NTS-Upstream Norm remain separate cards.)

---

**New here?** Start with the friendly card deck in [`HELP.md`](HELP.md). It distills the most common roles into 60-second actions.

---

## Long-form corpus notes (off the README first screen)

The [README](../README.md) first screen is the arrival. The sections below are the long-form invariant, roadmap, and build notes, relocated so a 60-second reader is not dumped a changelog. Gated status wording is unchanged.

## The invariant

**Over 5,100 theorems, every proof sealed with `Qed.` on just three
axioms** — the standard classical-reals trio Rocq ships with, none of
this corpus's own; `Axiom`, `Parameter`, and `admit.` appear nowhere.
There are **no `Admitted` theorems today** — both the deferred-proof and
counterexample registries are empty (the last deferred entry,
`arc_dot_max_at_endpoint`, was discharged 2026-07-01). CI fails any
unregistered `Admitted`. (The Flocq lane structurally inherits one
further axiom; details below.)

CI (`scripts/check_admitted.sh`) enforces a three-tier `Admitted`
discipline across both directories:

- **Tier 1** — an `Admitted` with no registry entry is a build failure.
  This is the default.
- **Tier 2** — an `Admitted` registered in
  [`docs/admitted-counterexamples.txt`](admitted-counterexamples.txt)
  is allowed permanently: the theorem *as stated* is false, with a
  verified counterexample on file. **None today — the counterexample
  registry is currently unpopulated.** The headline disproofs the registry once carried — Hobby Lemma
  4.3's no-proper-intersection half, and Shewchuk Theorem 13's general
  headline + O7 completeness (all **false as stated** because half-ulp
  `strict_succ_b64` is stronger than Shewchuk's bit-disjoint nonoverlapping) —
  have since been restated and **Qed-closed as disproof theorems** (no
  `Admitted` remains), in
  [`HobbyCounterexample_b64.v`](../theories-flocq/HobbyCounterexample_b64.v),
  [`B64_Shewchuk_Thm13_counterexample.v`](../theories-flocq/B64_Shewchuk_Thm13_counterexample.v),
  and [`docs/shewchuk-thm13-headline-counterexample.md`](shewchuk-thm13-headline-counterexample.md).
- **Tier 3** — an `Admitted` registered in
  [`docs/admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt)
  is allowed temporarily: the theorem is *true*, its proof structure is
  documented, and the remaining work is multi-session. **None today.**
  The last entry, `arc_dot_max_at_endpoint` (`theories/ArcSinglePeak.v` §2),
  a planar single-peak dot bound, was discharged 2026-07-01 via its
  documented chord-frame reduction — no external `psatz`/CSDP needed after
  all: in the chord frame the peak-side condition becomes a sign test on one
  coordinate, and a tangent bound plus a squared-magnitude comparison close
  the scalar core with only `ring`/`lra`/`nra`/`field` (the lemma gained the
  hypothesis `0 < dist S E`, true in every calling context via `valid_arc`).
  The earlier on-arc / sweep-clamp residuals
  (`point_to_arc_dist_radial_lower`, `point_to_arc_dist_fallback_ends_lower`,
  `point_to_arc_dist_centre_is_r` in `theories/ArcPointDistance.v`, the #64
  point-to-arc distance frontier) were discharged earlier. The registry's
  first-ever entry,
  `EdgeFaceBridge.H_bridge_core` (the planar same-face⇒bridge seam behind
  Phase 3's ring assembly), has been discharged via the planar Euler route:
  the bridge fact is now a named premise threaded through the EdgeFaceBridge
  chain and proved in `theories/HBridgeEuler.v` from the named planar Euler
  identity, so `extract_rings_valid` carries those Euler hypotheses as a
  conditional Qed with no `Admitted`. An entry comes off the registry only
  when the proof lands. (Hobby Lemma 4.3's no-proper-intersection half,
  Shewchuk Theorem 13's headline, and O7 completeness were previously here;
  each is now a Qed-closed disproof theorem — machine-checked **false** as
  stated, no `Admitted` remaining.)

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
against [`docs/axiom-allowlist.txt`](axiom-allowlist.txt), and
[`scripts/check_readme_axioms.sh`](../scripts/check_readme_axioms.sh)
guarantees the list above never drifts from that allowlist. The
allowlisted trio is the only *corpus-introduced* axiom set; host-lane
files on the exception list are not trio-clean. Sixteen `theories/`
files are listed in
[`docs/audit-exceptions.txt`](audit-exceptions.txt) because Stdlib
`atan` / `Ratan` / `sin_lt_x` pull `Classical_Prop.classic` (`InArc`,
`ArcLength`, `CurveBufferArea`, `ArcChord*`, `RelateArcAnalytic`,
`ArcSpanAtan2`, `ArcArcQuartic`, `Atan2`, `AngleBetween`, …).
`theories-flocq/` *additionally* inherits a fourth axiom,
`Classical_Prop.classic`, transitively from Flocq's binary-arithmetic
operations (`Binary.Bplus` / `Bminus` / `Bmult` carry it in their
definition closure) — a structural consequence of using Flocq as the
binary64 model, not a load-bearing axiom this corpus introduces. The
affected files are enumerated with per-file rationale in
[`docs/audit-exceptions.txt`](audit-exceptions.txt), and the policy
trade-offs are analysed in
[`docs/category-c-policy.md`](category-c-policy.md). No
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

The host `_CoqProject` builds 47 foundational `theories/` modules;
the container `_CoqProject.full` builds the entire corpus (521
registered modules — 432 in `theories/`, 89 in `theories-flocq/`).

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

**Modules atop the core primitives in active development.** Detailed histories live in `plan.md` (per-rung records) and the linked docs; this section only names the active threads and where each stands.

- **Curve-linearisation stack** — Linearise → Simplify → Tin → Validate (+ binary64 instance in `theories-flocq`), tracking the SQL/MM Spatial (ISO/IEC 13249-3) curve prototype.
- **Phase 0–7 chokepoint** — robust orientation (Shewchuk), intersection, snap-rounding/Hobby, OverlayNG, native curves (chord-approx Option B). Current Phase 0 frontier: Stage D expansion arithmetic. See the Roadmap table below.
- **Phase 5 FFI lane** (`libntsrocq`) — the Coq-extracted kernel is now callable **in-process** over a plain C ABI ([`oracle/nts_ffi.h`](../oracle/nts_ffi.h)), not only as the `oracle_bin` subprocess: 19 entry points (orientation — including the exact full-plane escalation for `UNCERTAIN`, `nts_rocq_orient_sign_exact` — intersection + point, hot-pixel filters, snap rounding, overlay labelling, in-circle, arc predicates, TwoSum / grow-expansion, simplifier), reference bindings for C# / C++ / Java ([`oracle/CONSUMERS.md`](../oracle/CONSUMERS.md)), and a parity gate that compares the FFI against the oracle protocol as raw IEEE 754 bit patterns. Soundness ledger per entry point (including what is sufficient-only or deferred) in [`docs/phase5-ffi-abi.md`](phase5-ffi-abi.md). Java lands on fork PR #7 (`feature/sfa-curve-rgr`); locationtech/jts is not a gate.
- **JCT seam** (`point_in_ring` / OverlayNG H1) — the interior predicate was refuted vacuous and restated over continuous paths; counterexamples hardened the guards (`ring_simple` + vertex-distinctness, `ray_avoids_vertices`, `no_horizontal_edge_at` shown necessary); the residual is the single named hypothesis `parity_characterises_interior_cont`. It is fully **discharged (unconditionally) for a family ladder** — rectangle, right triangle, general CCW triangle, diamond, convex hexagon — via a reusable IVT separation engine (`SeparationField` → `ConvexField`) and the monotone-chain parity machinery; the general convex case is CLOSED at the algebraic level: the bare `convex_no_interior_ymin` was refuted in degenerate position (`collinear_spike_not_convex_no_interior_ymin`, an honest negative), and `ConvexYUnimodal.v` §10 discharges the real content unconditionally under the honest strict-convexity guard (`convex_strict_start_y_unimodal` → `ConvexRayCrossing` → `ConvexJCT`, allowlist trio only); the algebraic `conv_min` form now lifts to the named two-component Prop `JCT_two_components_cont_simple` for every nonempty half-plane-presented convex ring (`JCTTwoComponentsConvex.convex_hp_jct_two_components_cont_simple`, first instance `diamond_jct_two_components_cont_simple`); the remaining gap is the same Prop on a general simple / taut non-convex ring. Entry points: [`docs/jct-proof-structure.md`](jct-proof-structure.md) and the counterexample docs beside it.
- **H-bridge / Euler campaign** (the `extract_rings_valid` lane) — **CLOSED (PRs #334–#363)**, now maintained by five parallel work tracks (#64–#68) coordinated by a sync thread. `euler_core_reduction` (the degree-≥2-core induction) is banked, and the transport premise is now **fully discharged**: `WalkResidualDischarge.v` proves `face_transport_premise_holds` and `H_bridge_premise_holds` outright under the five standing guards (per-vertex `fan_ok`, `no_spurs`, twin-aware no-crossing, no horizontal darts, twin-aware no-foreign-vertex) — the whole C-3 connector ladder (corridors on both sides, general fan corners, the corner/corridor bridge and rides, the orbit chain with end ties and parity close, the E-series per-step wiring) composes into one theorem with the standard axiom footprint. The Euler assembly is closed too: `EulerUnconditional.euler_characteristic_holds` proves the planar Euler identity V + F = E + 2C outright under the same guards (core peeling alternated with the same-face dispatch step, whose bridge branch consumes the Euler-free premise). The downstream threading is done too: `extract_rings_valid_of_guards` and `extract_rings_valid_holes_of_guards` (`theories-flocq/OverlayBridgeUnconditional.v`) restate ring extraction over the guard set alone — no Euler hypotheses anywhere in the lane. Full rung-by-rung record: `plan.md` § "Discharge campaign for `face_transport_premise`".
- **Showcases** — the **hat** and **Spectre** aperiodic monotiles (first fully-mechanized concave point-in-polygon classifications), the **hot-pixel ring** bridge back to Phase-2 snap-rounding, and the finite-stage **Besicovitch–Kakeya** Perron tree (`PerronStage`/`KakeyaOverlay`/`KakeyaExample`/`KakeyaSlide`; measure theory explicitly deferred).
- Companion modules (Real, Lattice, LineEq, etc.) ship alongside.

These feed the oracle consumed by [NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve).

See [`docs/HELP.md`](HELP.md) and [`docs/READING-GUIDE.md`](READING-GUIDE.md) for the documents that matter to your role (e.g. GIS Gus / BIM Bea → phase completion + audit files; Scholar Sam / Tech-Lead Tess → retros + proof-structure + seam maps; Newbie Nate → one completion doc + development-environment).

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
| Simplifier *(warm-up, not in the chokepoint sequence)* | `Validate_binary64.v` — greedy perpendicular-distance simplifier on binary64 + RocqRefRunner | Qed-closed structural (14 lemmas); soundness bridge deferred | **100%** — `Robust.Simplify.GreedyPerpSimplifier`, 262 / 262 tests bit-exact against RocqRefRunner; the `CP_BOUNDARY_SIMPLIFY` mode (surfaces wishlist #1) composes the extracted simplifier with `b64_orient_sign_filtered` to densify→simplify→orient a CurvePolygon boundary, tagging each corner INTSAFE (certified by `_sound_small_int`) vs APPROX (irrational arc vertices, interface-only) |
| 0 | `Orientation_b64.v` — Shewchuk-adaptive orientation under Flocq binary64 | Stage A filter Qed-closed (`b64_orient_sign_filtered`, decidability, totality, 5-constructor distinctness, NaN-safety); decoder consistency + cross_R soundness for integer regime `\|coord\| <= 2^25` Qed-closed (`Orient_b64_exact.v` — antisymmetry, all three vertex degeneracies, both cyclic permutations, headline `_sound_small_int`); Stage D expansion arithmetic now under construction (`B64_Expansion*`, `B64_FastExpansionSum*`, `Orient_b64_expansion.v`, `Orient_b64_stage_d.v` — sum-correctness Qed-closed, the general non-overlap headline a machine-checked counterexample, Qed-closed as a disproof (false as stated — [`B64_Shewchuk_Thm13_counterexample.v`](../theories-flocq/B64_Shewchuk_Thm13_counterexample.v)); specialised integer-safe headlines Qed-closed); **exact full-`binary64` orientation soundness now Qed-closed over the entire double-coordinate plane** (`Orient_b64_exact_full.v` — `b64_orient2d_exact_sound`, at three axioms, no `Classical_Prop.classic`), while the *fast* adaptive filter's general bounded-magnitude soundness (Stages B–D) stays deferred; the hybrid-filter hypothesis package (`OrientHybridPackage.v`) Qeds that pure binary64 orientation disagrees with the true sign (Hypothesis A), that this breaks strict CCW winding (A1), that a constantly-Uncertain + integer-exact hybrid is sound (B), and that any sound det-only filter must refuse the underflow observation class (C instance) — Ozaki / \(C\cdot\varepsilon\cdot M^2\) near-optimality remains a residual — see [`docs/soundness-strategy.md`](soundness-strategy.md), [`docs/audit-shewchuk-stages.md`](audit-shewchuk-stages.md), [`docs/jts-1093-orient-lane-2026-08.md`](jts-1093-orient-lane-2026-08.md) | **filter-complete** — `Robust.Orientation.RobustOrientation` (`Orient2d` / `Sign` / `SignFiltered` with 5-valued `OrientSignRobust`) bit-exact against RocqRefRunner `ORIENT` + `ORIENT_FILTERED` modes; `ORIENT_EXACT` provides the exact full-plane ground truth for the JTS #1106 differential test, and the same Qed-proven predicate is now extracted (oracle mode `ORIENT_EXACT_EXTRACTED`, FFI entry `nts_rocq_orient_sign_exact`) as the in-process escalation for `UNCERTAIN` |
| 1 | `Intersect_b64.v` + `Intersect_b64_exact.v` — robust segment intersection, predicate + coordinate | **shipped end-to-end** — five-valued `IntersectSign` filter on top of Phase 0's `b64_orient_sign_filtered`; structural lemmas Qed-closed (decidability, totality, 10-way distinctness, NaN propagation); integer-regime cross_R soundness for both `IntersectNone` and `IntersectPoint` via the R-side `strict_completeness` theorem in `theories/Intersect.v`; intersection-point projections (`b64_intersect_point_{x,y}`) with a Qed-closed forward-error bound in `K·eps` / condition-number form + soundness typeclass; `IntersectCollinear` sub-case disambiguation is the only remaining gap — see [`docs/phase1-completion.md`](phase1-completion.md), [`docs/phase1-c2-tight-retro.md`](phase1-c2-tight-retro.md) | **complete** — `Robust.Intersect.RobustLineIntersector` (`SignFiltered`, `IntersectPoint*`) bit-exact against RocqRefRunner `INTERSECT_FILTERED` / `INTERSECT_POINT_*` modes, 187 / 187 differential cases including integer-regime adversarial family |
| 2 | `SnapRounding_b64.v` / `HobbyTheorem_b64.v` — formal model of Hobby 1999 + Halperin-Packer 2002 (ISR) | **milestones 1–4 landed** — hot-pixel layer (`HotPixel.v` + `HotPixel_b64.v`) through the segment-touches-pixel filter, the Liang–Barsky parameter-interval filter, the passes-through relation (+ tight half-open variant), the snap-rounding correctness invariant (`SnapRounding_b64.v`), and the topological-correctness theorem at the supported level (`TopologicalCorrectness_b64.v`); Hobby Theorem 4.1 stated as a Qed-closed conditional with Lemma 4.2 closed and Lemma 4.3's no-proper half a Qed-closed disproof theorem ([`HobbyCounterexample_b64.v`](../theories-flocq/HobbyCounterexample_b64.v)) — see [`docs/audit-phase2-snap-rounding.md`](audit-phase2-snap-rounding.md), [`docs/phase2-hotpixel-progress.md`](phase2-hotpixel-progress.md), [`docs/hobby-theorem-proof-structure.md`](hobby-theorem-proof-structure.md) | oracle modes `PASSES_THROUGH_FILTER` / `PASSES_THROUGH_HALFOPEN` extracted |
| 3 | `OverlayNG` — topology graph + boolean overlay with labelling | **conditional headline Qed-closed** — `valid_geometry` + `boolean_op` (`Overlay.v`), the planar `TopologyGraph` + `build_graph` + labelling + `correct_labels_all_ops` (`OverlayGraph.v`), the snap-rounding noding bridge (`OverlayBridge.v`), and `overlay_ng_correct_conditional` (`OverlayCorrectness.v`) under three named hypotheses (JCT, DCEL ring-assembly = `extract_rings_valid`, now conditional-Qed modulo the registered `H_bridge_core` seam, semantic bridge); JCT seam work in `PointInRing*` — the prior `geometric_interior_stdlib` formulation is **refuted as vacuous** (`JordanCurveSeam.v : geometric_interior_stdlib_vacuous`) and restated over continuous paths, with the headline **H1 re-pointed onto `geometric_interior_cont`** and the canonical `JCT_two_components_cont` hypothesis now carrying the inter-component **separation clause** (sufficiency proved by `jct_cont_interior_is_geometric`); the continuous-component spine (`JCT.v`) then proves the equivalence-relation + bounded-component-invariance algebra, so the trapped-interior separation `no_path_from_interior_to_exterior` is a **free Qed corollary** (the sketch's "thesis-scale core" is in fact free), isolating the genuine remaining seam to `parity_characterises_interior_cont` behind the non-vacuous headline `point_in_ring_correct_jct_cont`; H1 is now closed for taut rings (`parity_seam_offring_taut`) and the two-component Prop itself is discharged for half-plane-presented convex rings (`JCTTwoComponentsConvex.v`) — still stated, not proved, for a general simple ring — see [`docs/jct-vacuity-finding.md`](jct-vacuity-finding.md), [`docs/jct-proof-structure.md`](jct-proof-structure.md), [`docs/h1-vacuity/`](h1-vacuity/), [`docs/audit-phase3-overlay.md`](audit-phase3-overlay.md), [`docs/audit-phase3-milestone5.md`](audit-phase3-milestone5.md) | oracle mode `EDGE_IN_RESULT` extracted |
| 4 | Native circular-arc primitives (chord-approximation / Option B) | **conditional headline Qed-closed** — `CurveGeometry` types + `to_geometry` bridge, `inCircle_R` / `arc_orient` (`ArcOrient.v`), arc-chord / arc-arc intersection (`ArcIntersect.v`) with the IVT gap closed (`ArcIntersectIVT.v`), `arc_in_hot_pixel` (`ArcHotPixel.v`), sagitta machinery (`ArcChordApprox.v`), and `arc_overlay_correct_chord_approx` (`ArcOverlay.v`) under named hypotheses; **Flocq in-circle soundness** (`InCircle_b64_exact.v` — full-plane sign + `2¹¹` integer-regime value exactness, PR #146) and **arc-line Scope A** (`ArcLineIntersect_b64_exact.v` — first-stage `sP`/`sQ`/`dx`/`dy` before division); native (non-chord) circular arithmetic remains far future — see [`docs/audit-phase4-curves.md`](audit-phase4-curves.md), [`docs/audit-phase4-chord-overfitting.md`](audit-phase4-chord-overfitting.md), [`docs/issue-64-arc-primitives-triage.md`](issue-64-arc-primitives-triage.md) | extracted oracle modes `INCIRCLE_SIGN` / `ARC_CHORD_CROSSES_CIRCLE` / `ARC_PASSES_THROUGH_PIXEL` (INCIRCLE backed by `b64_inCircle_B2R_sign_sound_small_int`) |
| 5 | Extraction toolchain + C# / C++ / Java FFI to production NTS · GEOS · JTS | **extraction toolchain shipped; in-process C ABI landed; three-language bindings shipped** — `Validate_binary64_extract.v` extracts 20 kernel functions with native-float overrides, and Phase 5 adds `libntsrocq` (`oracle/nts_ffi.{ml,h}` + `nts_ffi_stubs.c`): 19 of those functions callable in-process over a plain C ABI instead of forking `oracle_bin` per predicate. Gated by `oracle/gen_ffi_parity_tests.py` — ~1200 cases per run comparing the FFI against the oracle protocol as raw IEEE 754 bit patterns (NaN folded, `-0.0` distinguished), built + gated + published in CI. The exact escalation path for `UNCERTAIN` is now extracted and exposed (`nts_rocq_orient_sign_exact`, backed by the Qed-closed `b64_orient2d_exact_sound`; only the two IEEE 754 decode overrides are unverified glue, gated differentially against the independent zarith `ORIENT_EXACT`). Consumer façades: C# `RocqNative.cs`, C++ `RocqNative.hpp` (dlopen), Java `RocqNative.java` (JNA) — see [`oracle/CONSUMERS.md`](../oracle/CONSUMERS.md), [`docs/phase5-ffi-abi.md`](phase5-ffi-abi.md). Still open: the in-circle / passes-through exact counterparts, non-Linux native assets, and flipping production defaults onto the kernel | **bindings copied into consumers, defaults unchanged** — NTS Lab, GEOS header-only, JTS `jts-curve` on fork PR #7. `isAvailable()` skips when `libntsrocq` is absent. Official locationtech/jts is not the Java landing zone and is not a gate |
| 6 | Continuous integration of corpus against NTS test suite | pending Phase 5 (call-site integration) | 0% |
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
[`docs/audit-shewchuk-stages.md`](audit-shewchuk-stages.md).
Bottom line: Flocq 4.2.2 ships TwoSum, Dekker's TwoProduct, and
Veltkamp splitting; the missing piece is Shewchuk's expansion
arithmetic on top of those.

The critical-path piece identified in the audit — a binary64↔ℝ
bridge for the `b64_plus` / `b64_minus` / `b64_mult` helpers — is
now Qed-closed in
[`theories-flocq/B64_bridge.v`](../theories-flocq/B64_bridge.v).
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

The full dated, session-by-session forensic log — per-slice proof
narratives, forward-error derivations, Stage A/B/C/D notes — has been
moved to the phase-specific completion/audit docs and `docs/history/`
to keep this README scannable for all the defined actor roles
(collapsed from an initial 17 for overlap). See
[`docs/phase0-completion.md`](phase0-completion.md) and
[`docs/soundness-strategy.md`](soundness-strategy.md) for the
Shewchuk Stage A decoder-consistency and cross_R-soundness narrative
specifically, and the actor Reading Guide for the rest. Key
high-level outcomes remain in the Roadmap table above; the complete
session-by-session record is in the retros and `history/sessions/`
for Scholar Sam / Tech-Lead Tess / Joost the BDFL paths.

- **registry framework (in force since the Stage D / Phase 2-3
  engagement)**: the Flocq layer's `Admitted` theorems are governed by
  the three-tier discipline described in The invariant above —
  `scripts/check_admitted.sh` plus the
  [counterexample](admitted-counterexamples.txt) and
  [deferred-proof](admitted-deferred-proofs.txt) registries — and a
  per-theorem axiom audit (`scripts/audit_axioms.sh` +
  [`docs/axiom-allowlist.txt`](axiom-allowlist.txt) +
  [`docs/audit-exceptions.txt`](audit-exceptions.txt)) tracks the
  `Classical_Prop.classic` footprint inherited from Flocq's binary
  arithmetic.  See [`docs/category-c-policy.md`](category-c-policy.md).

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
- This is **not** complete. Current coverage is over 5,100 Qed-closed
  theorems across 521 registered `.v` modules (432 under `theories/` —
  47 of them in the host `_CoqProject` foundational target — plus 89
  modules under `theories-flocq/`). There are **no
  `Admitted` theorems today** — both the counterexample and
  deferred-proof registries are empty (see the registries and
  `scripts/check_admitted.sh`).
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

See [docs/HELP.md](HELP.md) and [docs/READING-GUIDE.md](READING-GUIDE.md) for which build path matches your actor/role (e.g. Newbie Nate vs. full Flocq for deep work). Also see [CONTRIBUTING.md](../CONTRIBUTING.md) and [docs/FOR-AI-AGENTS.md](FOR-AI-AGENTS.md).

### Local (macOS via Homebrew)

```sh
brew install rocq
rocq makefile -f _CoqProject -o Makefile.gen
make -f Makefile.gen
```

This builds the 47 foundational Stdlib-only modules in `_CoqProject`.
Modules with external dependencies (Flocq), plus the Stdlib-only Phase
3/4 modules built alongside them, live in `_CoqProject.full` and are
built inside the container only (see below).

CI (see [`.github/workflows/ci.yml`](../.github/workflows/ci.yml)) runs the
host build on `macos-latest`, then:

- `scripts/check_admitted.sh` — the three-tier `Admitted` check across
  **both** `theories/` and `theories-flocq/`: every `Admitted` must
  appear in exactly one registry (counterexample or deferred-proof);
  `Axiom`, `Parameter`, and `admit.` are hard failures.
- `scripts/check_readme_axioms.sh` — verifies this README's axiom list
  matches `docs/axiom-allowlist.txt` verbatim.

A second CI job builds the `_CoqProject.full` corpus inside the pinned
Rocq 9.2.0 + Flocq 4.2.2 container with `make --output-sync=target` (so
each file's output stays contiguous), incrementally on pull requests —
unchanged files are restored from a content-addressed cache — and from
clean on every push to `main`.  The output-synced log is split into
per-file `Print Assumptions` chunks cached alongside the `.vo` they
were compiled with; `scripts/audit_axioms.sh` then audits the assembled
chunks of **every** project file against the allowlist (file-level
exemptions from `docs/audit-exceptions.txt`), and a missing chunk for
any file fails the build, so audit coverage never silently shrinks.

### Containerised build (Rocq 9.2.0 + Flocq 4.2.2)

For modules that need [Flocq](https://flocq.gitlabpages.inria.fr/) (the
`theories-flocq/` corpus, linking the validation, orientation,
intersection, snap-rounding, and overlay layers to IEEE-754 binary64)
the canonical environment is a podman container based on the
official `rocq/rocq-prover:9.2.0-ocaml-4.14.2-flambda` image with
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
[`docs/development-environment.md`](development-environment.md)
for a host-install fallback that matches the container's package
versions exactly and builds locally on Ubuntu in ~5 minutes.

A successful `make` ends with `theories/*.vo` files and no errors. Each
`.vo` file is a kernel-checked term whose type is the corresponding theorem
statement. Build output also includes the `Print Assumptions` reports
(see The invariant above).

## Licence

BSD-3-Clause, matching NetTopologySuite's licence. See [LICENSE](../LICENSE).

NetTopologySuite is itself a derivative work of JTS Topology Suite, which
is dual-licensed under EPL 2.0 / EDL 1.0. The formal specifications in
this repository are derived from NTS source code; where that is the case,
the BSD-3-Clause grant respects NTS's attribution requirements.

## Contributing

See the full [CONTRIBUTING.md](../CONTRIBUTING.md) (and the actor-specific guidance in [docs/HELP.md](HELP.md) + [docs/READING-GUIDE.md](READING-GUIDE.md) + [docs/FOR-AI-AGENTS.md](FOR-AI-AGENTS.md) for agents).

The short version: new theorems must end with `Qed.` (or `Defined.`), respect the three-axiom + registry discipline, carry proper headers, and follow the documented session workflow for anything non-trivial. Joost is BDFL on corpus honesty and pruning, not product owner. Jeroen is PO. Pick your role card and contribute accordingly.
