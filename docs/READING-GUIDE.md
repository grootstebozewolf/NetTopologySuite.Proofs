# Reading guide — who reads what

**Note (HoTT pivot):** The detailed classical phase, audit, and proof-structure documents referenced below have been moved to `archive/docs/`. The personas and role-based navigation are deliberately preserved. New HoTT work (synthetic topology, univalent links to C# NetTopologySuite, etc.) will extend or replace paths over time. The archived material remains the essential reference for what has already been proved classically and for proof-engineering patterns.

The corpus's docs cover several actors with different reading needs.
This index maps each actor to their starting point and recommended
path through the docs.

Names are mnemonic — they alliterate with the role so they stick.

---

## 🌍 GIS Gus

**Role.** Uses NetTopologySuite for spatial computation; curious about
which geometric primitives have formal proofs.

**Start at.** Top-level `README.md` (HoTT pivot + vision), then (for historical classical results) in order under `archive/docs/`:

  1. `archive/docs/phase0-completion.md` — orient2d (Shewchuk Stage A robust
     orientation).
  2. `archive/docs/phase1-completion.md` — segment-pair intersection (filtered +
     exact + forward-error).
  3. `archive/docs/phase2-hotpixel-progress.md` — hot-pixel snap-rounding (the
     Phase 2 milestone progression).
  4. `archive/docs/audit-phase3-overlay.md` § headers — polygon overlay correctness
     (Union/Intersection/Difference/SymDiff).
  5. `archive/docs/audit-phase4-curves.md` § headers — arc/curve overlay status
     (SQL/MM CIRCULARSTRING; conditional headline lands, JCT gap
     precisely characterised).

**Skip (for now).** The deepest `archive/docs/history/sessions/` forensic traces unless you are doing comparative work or mining for lemmas to re-express in HoTT. The Shewchuk Theorem 13 deep-dives and Hobby-lemma docs remain research-grade references.

**Take away.** The (archived) corpus has Qed-closed soundness for orient2d, intersection, snap-rounding's preservation invariant, and conditional headlines for polygon overlay and curve overlay. Gaps are precisely named, not handwaved. The HoTT pivot aims to re-ground the key topological claims synthetically and add first-class C# linkage via equivalences.

---

## 🏗️ BIM Bea

**Role.** Models as-built geometry; cares about CIRCULARSTRING /
COMPOUNDCURVE / arc primitives.

**Start at.** `archive/docs/audit-phase4-curves.md`, then (historical classical):

  1. `archive/docs/audit-phase4-chord-overfitting.md` — the chord-approximation
     thesis direction (Option B).
  2. `archive/docs/point-in-ring-jct-path.md` — JCT path to `point_in_ring_correct`
     (relevant for ring-membership in valid polygons with arcs).
  3. Archived `archive/theories/ArcOrient.v`, `archive/theories/ArcIntersect.v`,
     `archive/theories/ArcHotPixel.v` file headers — the R-side arc
     predicates.
  4. Archived `archive/theories-flocq/ArcOrient_b64.v` etc. — the binary64
     mirrors.

**Skip.** Phase 0/1/2 unless you care about the underlying primitives (all archived).

**Take away.** Arc-overlay correctness landed conditionally in the classical corpus
(`arc_overlay_correct_chord_approx`); the b64 layer was verified up to
three registered Admitteds with documented discharge plans.

**Trust chain (classical).** The Phase 4 oracle modes (INCIRCLE_SIGN,
ARC_CHORD_CROSSES_CIRCLE, ARC_PASSES_THROUGH_PIXEL) were extracted directly
from the Coq layer (see archived `archive/oracle/driver.ml`). HoTT work will
revisit curve primitives with synthetic circle (S¹ HIT) and stronger linkage
to C# CIRCULARSTRING handling.

---

## 🛠️ Quality Gatekeeper (Max/Ruby)

**Role.** Keeps CI green, merges PRs, manages the deferred-proof
registry, owns the build pipeline details, and reviews PRs for
correctness and adherence to corpus discipline.

**Start at.** The new lightweight HoTT policy + archived classical material:

- [`../docs/axiom-policy.md`](../docs/axiom-policy.md) and root `README.md` § "Axiom policy (HoTT era)" — one axiom, generous, for new work.
- The archived four CI-enforced registries (under `archive/docs/`) when touching classical material:
  1. `archive/docs/axiom-allowlist.txt` — the three permitted axioms (classical era).
  2. `archive/docs/audit-exceptions.txt` — Category C per-file Classical_Prop pull
     exemptions.
  3. `archive/docs/admitted-deferred-proofs.txt` — registered Admitteds with
     discharge plans (classical).
  4. `archive/docs/admitted-counterexamples.txt` — registered Admitteds with
     verified-false statements.

**Also (archived).** `archive/.github/workflows/ci.yml` +
`archive/.github/workflows/build-oracle.yml`, the `archive/Dockerfile`,
`archive/docs/development-environment.md`.

**On classical-era PRs (if any).** The old `archive/scripts/check_admitted.sh` etc. were
the per-PR sanity net. (The HoTT era will define its own.)

**Reject (spirit).** Bare `admit` without justification, undocumented extra axioms (beyond the one generous allowance), hand-rolled OCaml when an extracted version exists, or wrappers with no new content. The HoTT era uses the lightweight "one axiom, let's be generous" policy from the root README; review focuses on the justification for that axiom + the actual C# equivalence/transport value rather than recreating the full classical audit theatre.

**Skip.** Per-session forensic traces in `archive/docs/history/sessions/` unless investigating a specific
Admitted's lineage.

**Take away.** The corpus's epistemic invariants are machine-checkable;
the gatekeeper's job is to keep the registries and pipeline in sync
with the `.v` files and review PRs against them. (CI Cara and Risk-Officer Rico responsibilities now live under this combined Quality Gatekeeper role.)

**When a new Admitted lands (classical material only).** Add an entry to
`archive/docs/admitted-deferred-proofs.txt` (provable, classical) or
`admitted-counterexamples.txt` (counterexample-blocked) with the
format:
`file:theorem_name | proof_structure_doc | section_references`.
The entry should include a discharge plan + consumer chain (which
downstream theorems use it). `archive/scripts/check_admitted.sh` validates
the registration on every (archived) CI run.

For new HoTT work the "one axiom, let's be generous" policy (root README) replaces the old heavy registry/audit theatre. The gatekeeper reviews the justification in the file header and the C# linkage value.

---

## 🎓 Scholar Sam (incl. Auditor Avery)

**Role.** Researches formal methods / mechanised geometry; evaluates
the corpus's methodology (including independent formal-methods audits
and trust-chain verification).

**Start at.** `archive/docs/slice-a-retro.md` and `archive/docs/slice-a-piece-5b-retro.md` —
engagement-level syntheses.

**Then in any order:**

  1. `archive/docs/audit-phase2-snap-rounding.md`, `archive/docs/audit-phase3-overlay.md`,
     `archive/docs/audit-phase3-milestone5.md`, `archive/docs/audit-phase4-curves.md`,
     `archive/docs/audit-shewchuk-stages.md` — per-phase proof-structure audits.
  2. `archive/docs/hobby-theorem-proof-structure.md`,
     `archive/docs/shewchuk-theorem-13-proof-structure.md` — proof structures for
     the named load-bearing theorems.
  3. `archive/docs/point-in-ring-seams-3-5-7-red.md` (or `archive/docs/point-in-ring-jct-path.md`),
     `archive/docs/point-in-ring-jct-path.md`,
     `archive/docs/point-in-ring-seam-attempts.md`,
     `archive/docs/point-in-ring-tangent-attempts.md` — the JCT / seven-seam analysis
     of `point_in_ring_correct` (Phase 5 work).
  4. `archive/docs/soundness-strategy.md`, `archive/docs/stage-d-feasibility.md`,
     `archive/docs/stage-d-retro.md`, `archive/docs/stage-d-chain-composition-approach.md` —
     soundness-strategy retrospectives.
  5. `archive/docs/history/sessions/*` — per-session forensic record (only
     when you need to verify the chronology or read precise stuck
     goals).
  6. The four (archived) registries + run `archive/scripts/audit_axioms.sh /tmp/full-build.log`
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

**Start at.** Top-level (new) `README.md` (HoTT pivot + roadmap vision).

**Then for historical "what was done" and to mine patterns:**

  - Archived top-level retros + `archive/docs/phase0-completion.md` etc. under `archive/docs/`.
  - `archive/docs/ecosystem-search-2026-05-29.md`, `archive/docs/point-in-ring-seams-3-5-7-red.md`.
  - Archived `archive/docs/admitted-deferred-proofs.txt` as the classical backlog.
  - `archive/docs/history/sessions/README.md` — index of per-session prompts + outcomes.

**Skip (for scoping new HoTT work).** Deep dives into classical-only seams unless you are porting a specific lemma.

**Take away.** The conditional-headline pattern and session discipline (1-3 deliverables, explicit stopping conditions, ~10% documented collapses) remain valuable. For the HoTT pivot the "backlog" becomes: which classical results do we re-prove synthetically, and which C# linkage equivalences do we establish first.

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
  - **Refactor phase**: clean up + review against the current policy (archived classical gauntlet in `archive/scripts/` when touching old material; for new HoTT work, the one-axiom justification + linkage claims per root README).
  - **Stopping conditions**: explicit full-success and tangent-stop
    criteria.
Use this template when proposing new sessions. The discipline of
stating stopping conditions up front prevents scope creep mid-session.

---



## 🌱 Newbie Nate (incl. Plain Reader Pete / 🧮 Rocq Rookie Ray)

**Role.** First contribution to the corpus; or casual reader who picked up the repo from a link and wants the elevator pitch; or absolute beginner with zero prior exposure to proof assistants (Rocq/Coq).

**Start at.** Top-level `README.md` (the HoTT pivot headline and vision for linking formal Coq to C# NTS) or the "Getting Started" section.

(If you have literally never seen a proof assistant before: open [`docs/pythagoras-for-beginners.v`](pythagoras-for-beginners.v) in an IDE (CoqIDE / VSCode + VSCoq) and step through it. It is deliberately self-contained, starts from `Record Point`, defines `dist_sq`, proves the 3-4-5 case first with `ring` then explicitly with asserts/rewrites for pedagogy, and pre-bunks "why spend so much compute on obvious geometry?". It has been lightly refreshed for the pivot; the classical "load-bearing chokepoints" discussion now also points forward to HoTT synthetic + equivalence work.)

**Then (for contributors / deeper dive into history or first HoTT steps):**

  1. (Historical) `archive/docs/development-environment.md` — how the classical toolchain was set up.
  2. Archived phase completion / audit docs under `archive/docs/` for context on what was already proved.
  3. (Future) the first HoTT modules + any "equivalence to C#" sketches once they exist.

**For your first PR (HoTT era).**
  - Small re-proofs of classical facts in HoTT style, or tiny equivalence/transport examples.
  - Or documentation / persona updates that help the next Newbie.

**Skip (initially).** The deepest `archive/docs/history/sessions/` cascades unless you are specifically mining them.

**Take away.** The bar is high but the discipline (and the welcoming pythagoras on-ramp) is documented. The shape of a good contribution is now "a clear HoTT statement + Qed + explicit link (even if partial) toward the C# side."

**Where to ask questions.** Open a GitHub Issue on this repo for
substantive questions; for "is this PR ready?" drop a comment on
the PR. Review cadence is typically same-day for PR triage, 1-3
days for full review.

---



## 🧑‍🔧 Tech-Lead Tess

**Role.** Designs new engagements, sequences sessions, decides
scope.

**Start at.** The archived retros (Scrum-Master Sara's path) under `archive/docs/` + the proof-structure docs (Scholar Sam's path) + top-level `README.md` HoTT roadmap.

**Then (for design patterns that still apply):**

  1. The archived `archive/docs/stage-d-*.md` cluster — design-route documentation for
     Stage D (a complex multi-route engagement).
  2. `archive/docs/history/sessions/slice-a-piece-5b-route1-design-session.md`
     — what a design-session artifact looks like.
  3. `archive/docs/point-in-ring-seams-3-5-7-red.md` (or `archive/docs/point-in-ring-jct-path.md`) — exemplar seam-map / JCT path work
     workflow for breaking down a thesis-scale problem.
  4. Archived `archive/docs/audit-phase3-milestone5.md` § 6 (Conditional strategy) — how
     the conditional-headline decision was made.
  5. Live `docs/hott-rgr-risk-cost-pivot.md` — new-era example of an RGR pivot on risk/cost
     (applied to choosing the linkage strategy for proving NTS ↔ HoTT proofs).

**Take away.** Design sessions produce mermaid diagrams + named-
hypothesis decompositions; implementation sessions discharge or
defer them. Two-route design (when uncertain) is documented as a
methodology. These patterns transfer directly to scoping HoTT modules and C# equivalence work.

**Methodology patterns to lean on.**
  - **Two-route design**: when the load-bearing approach is
    uncertain, design both routes in parallel. One typically
    collapses (e.g. Slice A Piece 5b Route 2 collapsed at Session
    2); the surviving route inherits the design insights.
  - **Seam map**: when a target theorem decomposes into N
    sub-problems, write each as a "seam" with what-exists / what's-
    missing / cost-per-seam. See
    `archive/docs/point-in-ring-seams-3-5-7-red.md` (or `archive/docs/point-in-ring-jct-path.md`) as the exemplar.
  - **Red/green workflow**: red = state simplest target + predicted
    tangents; green = attempt each, stop at first genuine tangent.
    The recent `archive/docs/point-in-ring-seams-3-5-7-red.md` +
    `archive/docs/point-in-ring-tangent-attempts.md` pair shows the cadence.

---

## 📦 Consumer Connie

**Role.** Downstream consumer (e.g. `.Curve` C# differential-test
runner, oracle binary user).

**Start at.** Top-level `README.md` (HoTT vision for C# linkage) + the archived `archive/oracle/driver.ml` head docstring (the classical protocol reference).

**Then (classical oracles — now archived):**

  1. `archive/oracle/driver.ml` file header — full protocol for all
     modes (SIMPLIFY, ORIENT, INTERSECT, PASSES_THROUGH,
     EDGE_IN_RESULT, INCIRCLE_SIGN, ARC_CHORD_CROSSES_CIRCLE,
     ARC_PASSES_THROUGH_PIXEL).
  2. Archived `.github/workflows/build-oracle.yml` — how `oracle_bin` was
     built and published.
  3. Archived Phase 4 audit + `Arc*_b64.v` headers for the trust
     chain of the Phase 4 modes.

**Skip.** Internal Coq proof structures — you trust the Qed (or the future HoTT equivalence).

**Take away (classical).** Each oracle mode either extracted directly from a
Coq-verified function or was hand-rolled with an explicit Coq pin
comment.

**Differential test pattern (historical reference).** The intended consumer workflow:
keep one long-running `oracle_bin` instance; the C# differential
runner sends a mode line + inputs over stdin; the binary replies
on stdout in hex-float format ("%h") so consumers can round-trip
bits exactly. In the HoTT era the emphasis shifts from "bit-exact oracle" to
"provable equivalence / transport between the Coq model and the NTS C# types".

---

## 🧭 NTS-Upstream Norm

**Role.** Writes NetTopologySuite code upstream; needs to know which
algorithms have proofs and what those proofs imply for behaviour.

**Start at.** Top-level `README.md` (HoTT pivot + C# linkage vision) + archived phase docs under `archive/docs/`.

**Then (classical correspondence — now historical reference):**

  1. Map each NTS algorithm to its (archived) corpus counterpart (see `archive/docs/`):
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

**Skip.** Coq proof internals. Read the file header's `WHAT THIS
FILE LANDS` block as the spec (all now in `archive/`).

**Take away (classical).** Proofs applied to the corpus's binary64 mirrors of NTS
algorithms. Bit-exact agreement held on documented int-safe inputs. The HoTT pivot's goal is stronger: not only "the oracle matched", but "here is the equivalence proof (or transport) between the C# implementation and the formal model."

---

## 🧠 Joost the BDFL (Joost mag het weten)

**Role.** The benevolent dictator for life and ultimate authority on the project. "Joost mag het weten" is the Dutch proverb ("only Joost knows" / "Joost may know it all"). He is assumed to have (or be able to quickly form) the complete picture of the corpus, its history, its gaps, and its long-term direction.

**Start at.** The full (new) top-level `README.md` (HoTT pivot vision + roadmap), the complete `READING-GUIDE.md`, every major archived retro and proof-structure document under `archive/docs/`, the entire `archive/docs/history/` tree (especially `sessions/`), the strategy and seam-map documents, and the archived CI/oracle material. You are the one actor whose path legitimately exercises the full archive (classical + the pivot decision). You also own the direction of the HoTT + C# linkage work.

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
| Newbie Nate (incl. Plain Reader Pete / Rocq Rookie Ray) | Casual reader / first contrib / zero-knowledge Coq on-ramp via pythagoras | `README.md` (pivot) + `pythagoras-for-beginners.v` | 1-5 min + example |
| GIS Gus             | GIS user                    | `README.md` → archived `archive/docs/phase[0-2]-*.md` | 30 min |
| BIM Bea             | BIM user                    | archived `archive/docs/audit-phase4-curves.md` | 1 h |
| Quality Gatekeeper (Max/Ruby) | HoTT build + one-axiom justification reviewer + C# linkage claims | `docs/axiom-policy.md` + root README "Axiom policy" + archived registries (when classical) | 20 min |
| Scholar Sam (incl. Auditor) | Formal-methods researcher + HoTT methodology + one-axiom + C# linkage audit | `docs/axiom-policy.md` + archived retros/registries | half day |
| Project Meta (Pat/Sara) | Roadmap / scope + session cadence | archived phases + retros + `archive/docs/history/sessions/` | 1-2 h |
| Tech-Lead Tess      | Engagement design           | archived retros + proof-structure / seam maps | half day |
| Consumer Connie / NTS-Upstream Norm | Oracle binary user or NTS upstream contributor | archived `archive/oracle/driver.ml` + (future HoTT C# linkage) | 15-60 min |
| Joost the BDFL      | Benevolent dictator for life (Joost mag het weten) | Full README + READING-GUIDE + entire `archive/` history tree | as needed |

(Note: several roles were collapsed for overlap after the initial 17-card list (Pete into Nate/Ray; CI Cara and Risk-Officer Rico into Quality Gatekeeper; Connie/Norm grouped) — see the cards above for the current grouping.)

---

**New here?** Start with the friendly card deck in [`HELP.md`](HELP.md). It distills the most common roles into 60-second actions. Also read [`docs/axiom-policy.md`](axiom-policy.md) (the "one axiom, let's be generous" rule). The classical deep docs are in `archive/docs/`. The HoTT work (and updated cards) are just starting.