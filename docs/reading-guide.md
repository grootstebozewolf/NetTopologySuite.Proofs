# Reading guide — who reads what

Maps each actor to a starting point and reading path.  Names alliterate
with the role.

---

## 🛣️ Plain Reader Pete

**Role.** Picked up the corpus from a link, wants the elevator pitch.

**Start at.** `README.md`.

**Stop after.** README's first three paragraphs.  The repo is "every
proof ends with `Qed`, no `Admitted`, only three classical axioms
allowed".  That's the headline.

**Next-up.** GIS algorithms → GIS Gus.  Curves/arcs → BIM Bea.
Contributing → Newbie Nate.

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

**Take away.** Qed-closed soundness for orient2d, intersection,
snap-rounding's preservation invariant; conditional headlines for
polygon and curve overlay.

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
(`arc_overlay_correct_chord_approx`); the b64 layer is verified up to
three registered Admitteds with documented discharge plans.

**Trust chain.** The Phase 4 oracle modes (INCIRCLE_SIGN,
ARC_CHORD_CROSSES_CIRCLE, ARC_PASSES_THROUGH_PIXEL) extract directly
from the Coq layer — they are no longer hand-rolled OCaml.  When a
mode says TRUE/FALSE, the Coq theorem behind it is identifiable from
the protocol docstring in `oracle/driver.ml`.

---

## 🛠️ Maintainer Max

**Role.** Keeps CI green, merges PRs, manages the deferred-proof
registry.

**Start at.** The four CI-enforced registries:

  1. `axiom-allowlist.txt` — the three permitted axioms.
  2. `audit-exceptions.txt` — Category C per-file Classical_Prop pull
     exemptions.
  3. `admitted-deferred-proofs.txt` — registered Admitteds with
     discharge plans.
  4. `admitted-counterexamples.txt` — registered Admitteds with
     verified-false statements.

**Then.** `category-c-policy.md` (currently Draft) +
`development-environment.md` (host-install fallback when Docker
fails).

**On every PR.** Run `scripts/check_admitted.sh`,
`scripts/audit_axioms.sh`, `scripts/check_readme_axioms.sh` — they're
the per-PR sanity net.

**Take away.** Keep the registries in sync with the `.v` files; the
CI scripts catch drift.

**When a new Admitted lands.** Add an entry to
`admitted-deferred-proofs.txt` (provable) or
`admitted-counterexamples.txt` (counterexample-blocked) with the
format:
`file:theorem_name | proof_structure_doc | section_references`.
The entry should include a discharge plan + consumer chain (which
downstream theorems use it).  `scripts/check_admitted.sh` validates
the registration on every CI run.

---

## 🎓 Scholar Sam

**Role.** Researches formal methods / mechanised geometry; evaluates
the corpus's methodology.

**Start at.** `slice-a-retro.md` and `slice-a-piece-5b-retro.md` —
engagement-level syntheses.

**Then in any order:**

  1. `audit-phase2-snap-rounding.md`, `audit-phase3-overlay.md`,
     `audit-phase3-milestone5.md`, `audit-phase4-curves.md`,
     `audit-shewchuk-stages.md` — per-phase proof-structure audits.
  2. `hobby-theorem-proof-structure.md`,
     `shewchuk-theorem-13-proof-structure.md` — proof structures for
     the named load-bearing theorems.
  3. `point-in-ring-correct-seam-map.md`,
     `point-in-ring-jct-path.md`,
     `point-in-ring-seam-attempts.md`,
     `point-in-ring-tangent-attempts.md` — the seven-seam analysis
     of `point_in_ring_correct` (Phase 5 work).
  4. `soundness-strategy.md`, `stage-d-feasibility.md`,
     `stage-d-retro.md`, `stage-d-chain-composition-approach.md` —
     soundness-strategy retrospectives.
  5. `docs/history/sessions/*` — per-session forensic record (only
     when you need to verify the chronology or read precise stuck
     goals).

**Take away.** Two patterns: the **conditional headline**
(Qed-closed under named thesis-shaped hypotheses) and the
**deferred-proof registry** (Admitted with discharge plan).  Both
make load-bearing gaps precise.

**Methodology meta-pattern.** Four headlines instantiate the
conditional pattern (`hobby_theorem_4_1_conditional`,
`overlay_ng_correct_conditional`, `arc_overlay_correct_chord_approx`,
`point_in_ring_correct_jct`).  The corpus's contribution is the
structural composition + precise naming of load-bearing gaps, not
their discharge.  Cite as such.

---

## 📋 Product-Owner Pat

**Role.** Decides what ships next, tracks phase completion, budgets
sessions.

**Start at.** `phase0-completion.md`, `phase1-completion.md`,
`phase2-hotpixel-progress.md` — what's done.

**Then for "what's next":**

  1. `ecosystem-search-2026-05-29.md` — JCT / Real.structure / atan2
     ecosystem audit; verdicts with cost estimates.
  2. `point-in-ring-seams-3-5-7-red.md` — most recent gap inventory
     for `point_in_ring_correct` with cost-per-seam.
  3. `admitted-deferred-proofs.txt` — every registered Admitted has
     a discharge plan + consumer chain; this is the next-work
     backlog.

**Skip.** Per-session outcomes — the retros aggregate them.

**Take away.** Budget per registry entry, not ad-hoc.  A session
lands 1-3 Qed-closed deliverables; ~10% collapse outright.
Multi-session engagements (Slice A Piece 5b ran 17; Phase 1
C.2-tight ran 6) close one entry.  Multiply estimated session count
by 1.5x for unknown unknowns.

---

## 🏃 Scrum-Master Sara

**Role.** Plans sessions, tracks cadence, retrospects on failed
sessions.

**Start at.** Top-level retros, then session traces:

  1. `slice-a-retro.md`, `slice-a-piece-5b-retro.md`,
     `phase1-c2-tight-retro.md`, `stage-d-retro.md` — engagement
     velocity, what worked, what didn't.
  2. `docs/history/sessions/README.md` — index of per-session
     prompts + outcomes (chronological).
  3. `docs/history/sessions/slice-a-piece-5b-route1-session-N-prompt.md`
     and the corresponding `-outcome.md` — prompt → outcome cadence
     for any session.

**Outcome vocabulary.** `LANDED` / `PARTIAL` / `COLLAPSED` against
declared deliverables.

**Session structure template** (five phases, use when proposing new
sessions):
  - **Grep first**: gather corpus state before writing.
  - **Red phase**: simplest target lemma + predicted tangents.
  - **Green phase**: deliverables in order, stop at first tangent.
  - **Refactor phase**: gauntlet (`check_admitted`, `audit_axioms`,
    `check_readme_axioms`).
  - **Stopping conditions**: explicit full-success + tangent-stop
    criteria.  Stating them up front prevents scope creep.

---

## 🔎 Reviewer Ruby

**Role.** Reviews PRs for correctness and adherence to corpus
discipline.

**Start at.** `README.md` § "The invariant" + the four CI registries
(Maintainer Max's list).

**Then in any PR:**

  1. Verify no new Admitteds without a registry entry
     (`check_admitted.sh`).
  2. Verify the new file's axiom footprint is allowlisted
     (`audit_axioms.sh`).
  3. Read the file header — it should declare audit footprint + any
     new axiom lineage.
  4. Cross-reference against the conditional-headline pattern: are
     load-bearing facts captured as Section Variables or registered
     Admitteds with documented discharge plans?

**Anti-patterns to reject.**
  - Bare `Admitted.` without registry entry.
  - Hand-rolled OCaml mirrors when an extracted version exists.
  - Wrappers around existing lemmas with no new content.

**Stacked PR cascades.** When sessions chain (Phase 4 A→B→C→D→E
= 5 stacked branches), review the BOTTOM PR first; the rest inherit
its content.  When the bottom merges, the next rebases onto main.

**Take away.** Epistemic discipline is the primary review axis;
code-quality is secondary.

---

## ⚙️ CI Cara

**Role.** Maintains the CI pipeline (rocq-flocq container, sequential
build, audit scripts, oracle extraction).

**Start at.** `.github/workflows/ci.yml` + `.github/workflows/build-oracle.yml`.

**Then:**

  1. `development-environment.md` — host-install fallback +
     toolchain pins (Rocq 9.1.1, Flocq 4.2.2, OCaml 4.14.2).
  2. `Dockerfile` — the container image both workflows reuse.
  3. `scripts/*.sh` — the three CI scripts that read the registries.

**Take away.** Two workflows on a shared Docker layer cache.  Adding
a CI step = script + invocation in `ci.yml` (or `build-oracle.yml`
for oracle-side).

**Oracle binary publication.** `build-oracle.yml` extracts +
links + uploads `oracle_bin` as a 90-day GitHub Actions artifact;
on `release` events it attaches to the release.  Downstream `.Curve`
consumes it via env var `ROCQ_REF_BIN`.

**Pinned vs host-install.** Pinned container is canonical
(`Dockerfile`); host-install (`development-environment.md`) is the
fallback when Docker is blocked.  Same `.vo` files either way; CI
runs the container.

---

## 🌱 Newbie Nate

**Role.** First contribution to the corpus.

**Start at.** `README.md` § "The invariant".

**Then in order:**

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

**Skip.** Slice A piece 5b cascade-invariant work — deep,
non-onboarding-friendly.

**Take away.** Read one full PR end-to-end (e.g. Phase 4 Session A)
to see the shape.

**Questions.** GitHub Issues for substantive questions; PR comments
for "is this ready?".  Triage: same-day; full review: 1-3 days.

---

## 🔬 Auditor Avery

**Role.** Independent formal-methods audit; needs to verify trust
chain claims.

**Start at.** `axiom-allowlist.txt` + `audit-exceptions.txt` +
`admitted-counterexamples.txt` + `admitted-deferred-proofs.txt` —
machine-checkable invariants.

**Then:**

  1. Run `scripts/audit_axioms.sh /tmp/full-build.log` against a
     fresh sequential `-j1` build.  Output should be `OK`.
  2. For each registered Admitted: trace its consumer chain (the
     theorems that USE it) and verify the chain is precise.
  3. Read the file header of each `theories-flocq/*_exact.v` —
     these are the chains discharging Admitteds.
  4. Check the trust chain end-to-end for any extracted code path
     (oracle modes): Coq theorem → extraction directive → OCaml
     symbol → runtime invocation.

**Skip.** Audit docs — they describe the methodology; verify
independently.

**Take away.** Load-bearing assumptions are precisely named and
CI-enforced.  Mechanical verification for structural invariants;
human verification for discharge-plan plausibility.

**Two-tier Admitted system.**
  - `admitted-counterexamples.txt`: theorem-as-stated is FALSE;
    counterexample verified.  Permanent.
  - `admitted-deferred-proofs.txt`: theorem is true; proof
    structure sketched.  Temporary — comes off when proof lands.
  - Removing a deferred-proof entry without proof violates the
    invariant; `check_admitted.sh` catches drift.

**Category C exemptions.** `audit-exceptions.txt` lists files
exempted from the strict axiom allowlist.  Transitional — each
file's `Classical_Prop` pull is inherited from the snap-rounding /
Flocq lineage.  Listing a new file requires PR justification.

---

## 🧑‍🔧 Tech-Lead Tess

**Role.** Designs new engagements, sequences sessions, decides
scope.

**Start at.** The retros (Scrum-Master Sara's path) + the
proof-structure docs (Scholar Sam's path).

**Then:**

  1. The `stage-d-*.md` cluster — design-route documentation for
     Stage D (a complex multi-route engagement).
  2. `slice-a-piece-5b-route1-design-session.md` (in `history/sessions/`)
     — what a design-session artifact looks like.
  3. `point-in-ring-correct-seam-map.md` — exemplar seam-map
     workflow for breaking down a thesis-scale problem.
  4. `audit-phase3-milestone5.md` § 6 (Conditional strategy) — how
     the conditional-headline decision was made.

**Methodology patterns.**
  - **Two-route design** (when the load-bearing approach is
    uncertain): design both in parallel; one typically collapses
    (Slice A Piece 5b Route 2 collapsed at Session 2), the survivor
    inherits the insights.
  - **Seam map** (when the target decomposes into N sub-problems):
    one seam per sub-problem with what-exists / what's-missing /
    cost.  Exemplar: `point-in-ring-correct-seam-map.md`.
  - **Red/green workflow**: red = simplest target + predicted
    tangents; green = attempt each, stop at first tangent.  See
    `point-in-ring-seams-3-5-7-red.md` +
    `point-in-ring-tangent-attempts.md`.

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

**Skip.** Internal Coq proof structures — trust the Qed.

**Take away.** Each oracle mode either extracts from a Coq function
or is hand-rolled with an explicit Coq pin comment.  Phase 4 modes
are extracted as of late May 2026.

**Differential test pattern.** Keep one long-running `oracle_bin`
instance; send mode line + inputs over stdin; read hex-float
("%h") output to round-trip bits exactly.  Persistent dispatch =
every mode except SIMPLIFY loops back.  Reference: Phase 0
`.Curve` C# port.

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
     - CIRCULARSTRING arc operations → Phase 4 `Arc*_b64.v`
       (conditional).
  2. Read the soundness theorem statement (not its proof) for the
     algorithm you're touching.

**Skip.** Coq proof internals.  Read the file header's `WHAT THIS
FILE LANDS` block as the spec.

**Take away.** Proofs apply to the corpus's binary64 mirrors of NTS
algorithms.  Bit-exact agreement holds on int-safe inputs (e.g.
|coord| <= 2^25 for orient2d, |coord| <= 2^11 for inCircle_R); on
mixed inputs, the filtered predicates give a sound 4-way
classification (POS / NEG / ZERO / UNCERTAIN) and callers must
fall back when UNCERTAIN.

---

## ⚖️ Risk-Officer Rico

**Role.** Compliance / risk; needs to know what's NOT guaranteed
before greenlighting downstream use.

**Start at.** `admitted-counterexamples.txt` — the verified-false
statements.  These are the explicit "this version of the theorem
is too strong" entries.

**Then:**

  1. `admitted-deferred-proofs.txt` — what's claimed but not yet
    formally proved.  Each entry includes a discharge plan; treat
    these as "the corpus believes this is true but hasn't
    machine-verified yet".
  2. `audit-exceptions.txt` — files exempted from the strict
    axiom allowlist; their soundness depends on
    `Classical_Prop.classic` transitively.
  3. The Phase 4 deferred Admitteds in particular:
    `b64_inCircle_R_exact`, `b64_minus_radius_bridge`,
    `b64_plus_radius_bridge`.  Each is registered with a concrete
    discharge plan.

**Skip.** Anything Qed-closed without a registry entry — that's the
trust-yes side.

**Take away — three Admitted tiers.**
  1. **Tier 1** (forbidden): bare `Admitted.` without registration —
     CI rejects.
  2. **Tier 2** (counterexample): theorem-as-stated is false;
     permanent; needs re-stating, not proving.
  3. **Tier 3** (deferred-proof): theorem is true; proof structure
     documented; temporary, closes when proof lands.

Risk surface = Tier 2 + Tier 3.  Both precisely characterised;
nothing is "sort of" verified.

---

## 🎯 Summary table

| Mnemonic | Role | First doc | Reading time |
|---|---|---|---|
| Plain Reader Pete   | Casual reader               | `README.md` (3 ¶)                      | 1 min |
| GIS Gus             | GIS user                    | `README.md` → `phase[0-2]-*.md`        | 30 min |
| BIM Bea             | BIM user                    | `audit-phase4-curves.md`               | 1 h |
| Maintainer Max      | Corpus maintainer           | `axiom-allowlist.txt` + registries     | 20 min |
| Scholar Sam         | Formal-methods researcher   | `slice-a-retro.md`                     | half day |
| Product-Owner Pat   | Roadmap / scope             | `phase*-completion.md`                 | 1 h |
| Scrum-Master Sara   | Session cadence             | top-level retros + `history/sessions/` | 1-2 h |
| Reviewer Ruby       | PR reviewer                 | README + registries                    | per PR |
| CI Cara             | Build infra                 | `ci.yml` + `build-oracle.yml`          | 30 min |
| Newbie Nate         | New contributor             | README + one phase completion          | 2 h |
| Auditor Avery       | External audit              | registries + run audit_axioms.sh       | 1 day |
| Tech-Lead Tess      | Engagement design           | retros + proof-structure docs          | half day |
| Consumer Connie     | Oracle binary user          | `oracle/driver.ml` header              | 15 min |
| NTS-Upstream Norm   | NetTopologySuite contributor| `README.md` + phase completions        | 1 h |
| Risk-Officer Rico   | Compliance / risk           | `admitted-counterexamples.txt`         | 30 min |
