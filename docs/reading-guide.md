# Reading guide — who reads what

The corpus's docs cover several actors with different reading needs.
This index maps each actor to their starting point and recommended
path through the docs.

Names are mnemonic — they alliterate with the role so they stick.

---

## 🛣️ Plain Reader Pete

**Role.** Picked up the corpus from a link, wants the elevator pitch.

**Start at.** `README.md`.

**Stop after.** README's first three paragraphs.  The repo is "every
proof ends with `Qed`, no `Admitted`, only three classical axioms
allowed".  That's the headline.

**Read further if you ever want to:** understand what's mechanically
proved about computational geometry algorithms.  Then graduate to
GIS Gus's path.

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

**Skip.** Anything under `docs/history/sessions/` (forensic), the
Shewchuk Theorem 13 deep-dives (research-grade), and the Hobby-lemma
docs (cell-snap-rounding internals).

**Take away.** The corpus has Qed-closed soundness for orient2d,
intersection, snap-rounding's preservation invariant, and a
conditional headline for polygon overlay.

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

**Skip.** Per-session forensic traces unless investigating a specific
Admitted's lineage.

**Take away.** The corpus's epistemic invariants are machine-checkable;
the maintainer's job is to keep the registries in sync with the
`.v` files and review PRs against them.

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

**Take away.** Two patterns to watch: the **conditional headline**
(Qed-closed theorem under named thesis-shaped hypotheses) and the
**deferred-proof registry** (Admitted with documented discharge
plan).  Both make load-bearing gaps precise.

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

**Take away.** The conditional-headline pattern means "what's the
next thesis-scale gap to discharge or the next library to import" is
the right next-work granularity.  Don't budget for ad-hoc work; budget
for one registry entry at a time.

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

**Pattern to look for.** The session prompts use a "Red phase / Green
phase / Refactor phase / Stopping conditions" structure.  Outcomes
report `LANDED` / `PARTIAL` / `COLLAPSED` against deliverables.

**Take away.** Sessions average 1-3 deliverables; collapses happen
~10% of the time and are documented; the cadence is stable.

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

**Take away.** The corpus's epistemic discipline is the primary
review axis.  Code-quality review is secondary.

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

**Skip.** Anything mathematical.

**Take away.** The pipeline is two workflows on a shared Docker layer
cache.  Adding a CI step means adding a script + an invocation in
`ci.yml` (or `build-oracle.yml` for oracle-side changes).

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

**Skip.** The Slice A piece 5b cascade-invariant work — it's deep and
non-onboarding-friendly.

**Take away.** The bar is high but the discipline is documented.
Read one full PR (e.g. the recent Phase 4 Session A) to see the
shape.

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

**Skip.** Audit docs (they describe the methodology); your job is to
verify it independently.

**Take away.** The corpus's load-bearing assumptions are precisely
named and CI-enforced.  Independent verification is mechanical for
the structural invariants and human for the discharge-plan
plausibility.

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

**Take away.** Design sessions produce mermaid diagrams + named-
hypothesis decompositions; implementation sessions discharge or
defer them.  Two-route design (when uncertain) is documented as a
methodology.

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
comment.  Phase 4 modes recently swapped from hand-rolled to
extracted (commit `bd6d01f` on `claude/oracle-arc-extracted`).

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
