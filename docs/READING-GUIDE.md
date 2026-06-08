# Reading guide — who reads what

The corpus's docs cover several actors with different reading needs.
This index maps each actor to their starting point and recommended
path through the docs.

Names are mnemonic — they alliterate with the role so they stick.

---

## 🌍 GIS Gus

**Role.** Uses NetTopologySuite for spatial computation; curious about
which geometric primitives have formal proofs.

**Start at.** `README.md`, then in order:

  1. `phase0-completion.md` — orient2d (Shewchuk Stage A robust
     orientation).
  2. `phase1-completion.md` — segment-pair intersection (filtered +
     exact + forward-error).
  3. `phase2-hotpixel-progress.md` — hot-pixel snap-rounding (the
     Phase 2 milestone progression).
  4. `audit-phase3-overlay.md` § headers — polygon overlay correctness
     (Union/Intersection/Difference/SymDiff).
  5. `audit-phase4-curves.md` § headers — arc/curve overlay status
     (SQL/MM CIRCULARSTRING; conditional headline lands, JCT gap
     precisely characterised).

**Skip.** Anything under `docs/history/sessions/` (forensic), the
Shewchuk Theorem 13 deep-dives (research-grade), and the Hobby-lemma
docs (cell-snap-rounding internals).

**Take away.** The corpus has Qed-closed soundness for orient2d,
intersection, snap-rounding's preservation invariant, and conditional
headlines for polygon overlay and curve overlay. Gaps are precisely
named, not handwaved.

---

## 🏗️ BIM Bea

**Role.** Models as-built geometry; cares about CIRCULARSTRING /
COMPOUNDCURVE / arc primitives.

**Start at.** `audit-phase4-curves.md`, then:

  1. `audit-phase4-chord-overfitting.md` — the chord-approximation
     thesis direction (Option B).
  2. `point-in-ring-jct-path.md` — JCT path to `point_in_ring_correct`
     (relevant for ring-membership in valid polygons with arcs).
  3. `theories/ArcOrient.v`, `theories/ArcIntersect.v`,
     `theories/ArcHotPixel.v` file headers — the R-side arc
     predicates.
  4. `theories-flocq/ArcOrient_b64.v`,
     `theories-flocq/ArcIntersect_b64.v`,
     `theories-flocq/ArcHotPixel_b64.v` file headers — the binary64
     mirrors.

**Skip.** Phase 0/1/2 unless you care about the underlying primitives.

**Take away.** Arc-overlay correctness lands conditionally
(`arc_overlay_correct_chord_approx`); the b64 in-circle layer now has
Qed-closed sign + integer-regime value exactness (`InCircle_b64_exact.v`,
PR #146). Arc-line coordinates are Scope A only (`ArcLineIntersect_b64_exact.v`
— `sP`/`sQ`/`dx`/`dy` before division).

**Trust chain.** The Phase 4 oracle modes (INCIRCLE_SIGN,
ARC_CHORD_CROSSES_CIRCLE, ARC_PASSES_THROUGH_PIXEL) extract directly
from the Coq layer — they are no longer hand-rolled OCaml. INCIRCLE_SIGN
is backed by `b64_inCircle_B2R_sign_sound_small_int` at `|coord| <= 2^11`
(degree-4 chain; tighter than orient2d's `2^25`). When a mode says
TRUE/FALSE, the Coq theorem behind it is identifiable from the protocol
docstring in `oracle/driver.ml` and `docs/verified-claims.md`.

---

## 🛠️ Quality Gatekeeper (Max/Ruby)

**Role.** Keeps CI green, merges PRs, manages the deferred-proof
registry, owns the build pipeline details, and reviews PRs for
correctness and adherence to corpus discipline.

**Start at.** The four CI-enforced registries:

  1. `axiom-allowlist.txt` — the three permitted axioms.
  2. `audit-exceptions.txt` — Category C per-file Classical_Prop pull
     exemptions.
  3. `admitted-deferred-proofs.txt` — registered Admitteds with
     discharge plans.
  4. `admitted-counterexamples.txt` — registered Admitteds with
     verified-false statements.

**Also.** [`.github/workflows/ci.yml`](../.github/workflows/ci.yml) +
`build-oracle.yml`, the `Dockerfile`, `docs/development-environment.md`.

**On every PR.** Run `scripts/check_admitted.sh`,
`scripts/audit_axioms.sh`, `scripts/check_readme_axioms.sh` — they're
the per-PR sanity net.

**Reject.** Bare `Admitted.` without registry entry, hand-rolled OCaml
when an extracted version exists, or wrappers with no new content.

**Skip.** Per-session forensic traces unless investigating a specific
Admitted's lineage.

**Take away.** The corpus's epistemic invariants are machine-checkable;
the gatekeeper's job is to keep the registries and pipeline in sync
with the `.v` files and review PRs against them. (CI Cara and Risk-Officer Rico responsibilities now live under this combined Quality Gatekeeper role.)

**When a new Admitted lands.** Add an entry to
`admitted-deferred-proofs.txt` (provable) or
`admitted-counterexamples.txt` (counterexample-blocked) with the
format:
`file:theorem_name | proof_structure_doc | section_references`.
The entry should include a discharge plan + consumer chain (which
downstream theorems use it). `scripts/check_admitted.sh` validates
the registration on every CI run.

---

## 🎓 Scholar Sam (incl. Auditor Avery)

**Role.** Researches formal methods / mechanised geometry; evaluates
the corpus's methodology (including independent formal-methods audits
and trust-chain verification).

**Start at.** `slice-a-retro.md` and `slice-a-piece-5b-retro.md` —
engagement-level syntheses.

**Then in any order:**

  1. `audit-phase2-snap-rounding.md`, `audit-phase3-overlay.md`,
     `audit-phase3-milestone5.md`, `audit-phase4-curves.md`,
     `audit-shewchuk-stages.md` — per-phase proof-structure audits.
  2. `hobby-theorem-proof-structure.md`,
     `shewchuk-theorem-13-proof-structure.md` — proof structures for
     the named load-bearing theorems.
  3. `point-in-ring-seams-3-5-7-red.md` (or `point-in-ring-jct-path.md`),
     `point-in-ring-jct-path.md`,
     `point-in-ring-seam-attempts.md`,
     `point-in-ring-tangent-attempts.md` — the JCT / seven-seam analysis
     of `point_in_ring_correct` (Phase 5 work).
  4. `soundness-strategy.md`, `stage-d-feasibility.md`,
     `stage-d-retro.md`, `stage-d-chain-composition-approach.md` —
     soundness-strategy retrospectives.
  5. `docs/history/sessions/*` — per-session forensic record (only
     when you need to verify the chronology or read precise stuck
     goals).
  6. The four registries + run `scripts/audit_axioms.sh /tmp/full-build.log`
     (for trust-chain / axiom footprint audits).

**Take away.** Two patterns to watch: the **conditional headline**
(Qed-closed theorem under named thesis-shaped hypotheses) and the
**deferred-proof registry** (Admitted with documented discharge
plan). Both make load-bearing gaps precise.

**Methodology meta-pattern.** Four current headlines instantiate
the conditional pattern (`hobby_theorem_4_1_conditional`,
`overlay_ng_correct_conditional`, `arc_overlay_correct_chord_approx`,
`point_in_ring_correct_jct`). Each is Qed-closed under 2-3 named
thesis-shaped hypotheses; the corpus's contribution is the
structural composition plus the precise naming of the load-bearing
gaps, not the discharge of those gaps. This pattern is the corpus's
shipping discipline; cite as such.

**Tiers (when auditing).** Forbidden / counterexample / deferred-proof.

---

## 📋 Project Meta (Pat/Sara)

**Role.** Decides what ships next, tracks phase completion, budgets
sessions, plans cadence, and retrospects on how the work actually went.

**Start at.** Top-level retros + `phase0-completion.md`,
`phase1-completion.md`, `phase2-hotpixel-progress.md` — what's done.

**Then for "what's next" and cadence:**

  1. `ecosystem-search-2026-05-29.md` — JCT / Real.structure / atan2
     ecosystem audit; verdicts with cost estimates.
  2. `point-in-ring-seams-3-5-7-red.md` — most recent gap inventory
     for `point_in_ring_correct` with cost-per-seam.
  3. `admitted-deferred-proofs.txt` — every registered Admitted has
     a discharge plan + consumer chain; this is the next-work
     backlog.
  4. `docs/history/sessions/README.md` — index of per-session
     prompts + outcomes (chronological).

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

**Start at.** `README.md` (first three paragraphs for the headline: "every proof ends with `Qed`, no `Admitted`, only three classical axioms allowed") or `README.md` § "The invariant" for contributors.

(If you have literally never seen a proof assistant before: open [`docs/pythagoras-for-beginners.v`](pythagoras-for-beginners.v) in an IDE (CoqIDE / VSCode + VSCoq) and step through it. It is deliberately self-contained, starts from `Record Point`, defines `dist_sq`, proves the 3-4-5 case first with `ring` then explicitly with asserts/rewrites for pedagogy, and pre-bunks "why spend so much compute on obvious geometry?": even Pythagoras is non-trivial once every algebraic step must be justified from the axioms; the load-bearing chokepoints like orientation/intersection/snap-rounding are what justify the engineering investment.)

A second gentle on-ramp is [`docs/sqrt3-irrational-for-beginners.v`](sqrt3-irrational-for-beginners.v).  It proves the classical fact that `sqrt 3` is irrational by Fermat-style infinite descent over the integers, then lifts the result to the reals.  The file contains an unusually explicit "honesty note" explaining that this number-theoretic fact is *not* used by the geometric work in the corpus (the hex embeddings keep `sqrt 3` explicitly and discharge the necessary arithmetic with `lra`/`nra`/`field`).  It is included purely as a teaching example of descent and of moving between `Z` and `R`.

**Then (for contributors / deeper dive):**

  1. `development-environment.md` — get the toolchain running.
  2. Any one Phase completion doc that touches your area of interest.
  3. The corresponding `audit-*.md` for that phase.
  4. A short Qed-closed file (e.g. `theories/ArcIntersect.v`, ~200
     lines) — read end-to-end as a sample.

**For your first PR.**
  - Pick the smallest Admitted in `admitted-deferred-proofs.txt`
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
     Stage D (a complex multi-route engagement).
  2. `docs/history/sessions/slice-a-piece-5b-route1-design-session.md`
     — what a design-session artifact looks like.
  3. `point-in-ring-seams-3-5-7-red.md` (or `point-in-ring-jct-path.md`) — exemplar seam-map / JCT path work
     workflow for breaking down a thesis-scale problem.
  4. `audit-phase3-milestone5.md` § 6 (Conditional strategy) — how
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
    `point-in-ring-seams-3-5-7-red.md` (or `point-in-ring-jct-path.md`) as the exemplar.
  - **Red/green workflow**: red = state simplest target + predicted
    tangents; green = attempt each, stop at first genuine tangent.
    The recent `point-in-ring-seams-3-5-7-red.md` +
    `point-in-ring-tangent-attempts.md` pair shows the cadence.

---

## 📦 Consumer Connie

**Role.** Downstream consumer (e.g. `.Curve` C# differential-test
runner, oracle binary user).

**Start at.** `README.md` + `oracle/driver.ml` head docstring (the
protocol reference).

**Then:**

  1. The `oracle/driver.ml` file header — full protocol for all
     modes (SIMPLIFY, ORIENT, INTERSECT, PASSES_THROUGH,
     EDGE_IN_RESULT, INCIRCLE_SIGN, ARC_CHORD_CROSSES_CIRCLE,
     ARC_PASSES_THROUGH_PIXEL).
  2. `.github/workflows/build-oracle.yml` — how `oracle_bin` is
     built and published.
  3. The Phase 4 audit + recent `Arc*_b64.v` headers for the trust
     chain of the Phase 4 modes.

**Skip.** Internal Coq proof structures — you trust the Qed.

**Take away.** Each oracle mode either extracts directly from a
Coq-verified function or is hand-rolled with an explicit Coq pin
comment. Phase 4 modes recently swapped from hand-rolled to
extracted (commit `bd6d01f` on `claude/oracle-arc-extracted`).

**Differential test pattern.** The intended consumer workflow:
keep one long-running `oracle_bin` instance; the C# differential
runner sends a mode line + inputs over stdin; the binary replies
on stdout in hex-float format ("%h") so consumers can round-trip
bits exactly. Persistent-mode dispatch is the design (every mode
except SIMPLIFY loops back). See Phase 0 `.Curve` C# port for the
reference implementation.

---

## 🧭 NTS-Upstream Norm

**Role.** Writes NetTopologySuite code upstream; needs to know which
algorithms have proofs and what those proofs imply for behaviour.

**Start at.** `README.md` § "The invariant" + the four phase-
completion docs (`phase0-completion.md`, `phase1-completion.md`,
`phase2-hotpixel-progress.md`, audit-phase3-overlay.md).

**Then:**

  1. Map each NTS algorithm to its corpus counterpart:
     - `RobustLineIntersector` → `b64_intersect_*` (Phase 0/1).
     - `RobustDeterminant` → `b64_orient2d` + Stage A filter (Phase 0).
     - `HotPixel` snap-rounding → `b64_in_hot_pixel` + snap-round
       preservation (Phase 2).
     - `OverlayNG` boolean ops → `overlay_ng_correct_conditional`
       (Phase 3, conditional).
     - CIRCULARSTRING arc operations → Phase 4 `Arc*_b64.v` +
       `InCircle_b64_exact.v` / `ArcLineIntersect_b64_exact.v`
       (in-circle exact at `|coord| <= 2^11`; arc-line Scope A).
  2. Read the soundness theorem statement (not its proof) for the
     algorithm you're touching.

**Skip.** Coq proof internals. Read the file header's `WHAT THIS
FILE LANDS` block as the spec.

**Take away.** Proofs apply to the corpus's binary64 mirrors of NTS
algorithms. Bit-exact agreement holds on int-safe inputs (e.g.
|coord| <= 2^25 for orient2d, |coord| <= 2^11 for inCircle_R); on
mixed inputs, the filtered predicates give a sound 4-way
classification (POS / NEG / ZERO / UNCERTAIN) and callers must
fall back when UNCERTAIN.

---

## 🧠 Joost the BDFL (Joost mag het weten)

**Role.** The benevolent dictator for life and ultimate authority on the project. "Joost mag het weten" is the Dutch proverb ("only Joost knows" / "Joost may know it all"). He is assumed to have (or be able to quickly form) the complete picture of the corpus, its history, its gaps, and its long-term direction.

**Start at.** The full `README.md` (including all status and the embedded catalogue), the complete `READING-GUIDE.md`, every major retro and proof-structure document, the entire `docs/history/` tree (especially `sessions/`), the strategy and seam-map documents, and the CI/oracle credibility material. You are the one actor whose path legitimately exercises the archive.

**Special power.** Final say on:
- Whether a marginal file stays at top level or moves to history/.
- Scope and priority of new engagements.
- Tie-breakers when the strict "useful for one of the other defined actors" rule is in conflict with institutional memory or future utility.
- Architecture and "what the project is" questions.

In pruning work, Joost is the explicit exception to the actor filter and the person who reviews the stop-condition batch results.

**Take away.** You know (or can find out) why every artifact exists and where it lives. Your job includes making sure the other actors have the right on-ramps and that nothing important is lost in the archive.

---

## 🎯 Summary table

| Mnemonic | Role | First doc | Reading time |
|---|---|---|---|
| Newbie Nate (incl. Plain Reader Pete / Rocq Rookie Ray) | Casual reader / first contrib / zero-knowledge Coq on-ramp via pythagoras + sqrt3 example | `README.md` (3 ¶) + `pythagoras-for-beginners.v` + `sqrt3-irrational-for-beginners.v` + dev-env | 1-10 min + examples |
| GIS Gus             | GIS user                    | `README.md` → `phase[0-2]-*.md`        | 30 min |
| BIM Bea             | BIM user                    | `audit-phase4-curves.md`               | 1 h |
| Quality Gatekeeper (Max/Ruby) | Corpus maintainer + PR reviewer + CI/Risk | `axiom-allowlist.txt` + registries + `ci.yml` | 20 min |
| Scholar Sam (incl. Auditor) | Formal-methods researcher + independent audit | `slice-a-retro.md` + registries + audit script | half day |
| Project Meta (Pat/Sara) | Roadmap / scope + session cadence | `phase*-completion.md` + top-level retros + `history/sessions/` | 1-2 h |
| Tech-Lead Tess      | Engagement design           | retros + proof-structure docs / seam maps | half day |
| Consumer Connie / NTS-Upstream Norm | Oracle binary user or NTS upstream contributor | `oracle/driver.ml` header + phase completions | 15-60 min |
| Joost the BDFL      | Benevolent dictator for life (Joost mag het weten) | Full README + READING-GUIDE + entire history/ tree | as needed |

(Note: several roles were collapsed for overlap after the initial 17-card list (Pete into Nate/Ray; CI Cara and Risk-Officer Rico into Quality Gatekeeper; Connie/Norm grouped) — see the cards above for the current grouping.)

---

**New here?** Start with the friendly card deck in [`HELP.md`](HELP.md). It distills the most common roles into 60-second actions.