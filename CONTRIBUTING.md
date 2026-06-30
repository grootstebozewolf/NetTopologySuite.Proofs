# Contributing to NetTopologySuite.Proofs

Thank you for your interest in contributing to this corpus of mechanically-verified Rocq proofs for NetTopologySuite / JTS geometry algorithms.

**The non-negotiable rule (enforced by CI and the consolidated actor roles' paths):**

> Every theorem must end with `Qed.` (or `Defined.` for computable terms).  
> No bare `Admitted`, no `Axiom`, no `Parameter`, no `admit.` tactic in the `.v` files.  
> The only exception today is the single registered `Admitted` entry — 1 deferred proof (`arc_dot_max_at_endpoint`) in `admitted-deferred-proofs.txt`, with a concrete seam on file and discharge plan; the counterexample registry (`admitted-counterexamples.txt`) is currently unpopulated. Any `Admitted` must appear in one of those two registries or CI fails.

The [Reading Guide](docs/READING-GUIDE.md) and friendly [Help cards](docs/HELP.md) define the consolidated actor roles (lightly collapsed from an original 17 for overlap) and exactly what each should read (and what to skip). Use them to orient yourself.

## Quick start for different contributor types

See your role in [docs/HELP.md](docs/HELP.md) (or the full [docs/READING-GUIDE.md](docs/READING-GUIDE.md)):

- **Newbie Nate** (first contribution): Start with `README.md` § "The invariant", then `docs/development-environment.md`. If you have literally never used a proof assistant, open `docs/pythagoras-for-beginners.v` first and step through it. Then pick the smallest entry in `admitted-deferred-proofs.txt` whose discharge plan you understand. Or a "WHAT IS QED-CLOSED / WHAT REMAINS OPEN" item from one of the audit docs. First PRs are typically small lemmas that close part of a registered deferred proof.

- **Tech-Lead Tess / Product-Owner Pat** (designing engagements, scoping): Work from the retros (`slice-a-retro.md`, `slice-a-piece-5b-retro.md`, `phase*-retro.md`, `stage-d-retro.md`), seam maps (`point-in-ring-seams-3-5-7-red.md` or `point-in-ring-jct-path.md`), and proof-structure docs (`hobby-theorem-proof-structure.md`, `shewchuk-theorem-13-proof-structure.md`). Use the "Red / Green / Refactor / Stopping conditions" template when proposing sessions. Two-route design and explicit "named hypotheses" for conditional headlines are the current methodology.

- **Scholar Sam** (researcher / methodology auditor): The retros + proof-structure + audit-*.md files + the full `docs/history/sessions/` tree when you need chronology. Pay special attention to the "conditional headline" pattern (Qed-closed under explicitly named thesis-shaped hypotheses) and the deferred-proof registry discipline.

- **Scrum-Master Sara** (cadence, retros): Top-level retros + `docs/history/sessions/README.md`. Look for the prompt/outcome cadence and the ~10% collapse rate that is always documented.

- **Reviewer Ruby / Maintainer Max / Auditor Avery / Risk-Officer Rico / CI Cara**: The four CI-enforced registries first (`admitted-deferred-proofs.txt`, `admitted-counterexamples.txt`, `axiom-allowlist.txt`, `audit-exceptions.txt`). Run `scripts/check_admitted.sh`, `scripts/audit_axioms.sh`, and `scripts/check_readme_axioms.sh` on every PR. Also inspect `.github/workflows/ci.yml` + `build-oracle.yml`, the `Dockerfile`, `docs/development-environment.md`. Reject bare `Admitted`, hand-rolled OCaml when an extracted version exists, or wrappers with no new content. Stacked PR cascades are reviewed bottom-up.

- **Consumer Connie / NTS-Upstream Norm**: `oracle/driver.ml` header (the protocol) + the phase completion docs that map NTS algorithms to their verified mirrors. Bit-exact agreement claims are limited to the documented integer-safe regimes.

- **Joost the BDFL (Joost mag het weten)**: You already know (or will quickly form) the complete picture. You have final say on scope, architecture, what stays at top-level `docs/` vs. `history/`, and any tie-breakers during pruning or design. Your path legitimately includes the entire archive.

- **GIS Gus / BIM Bea / Newbie Nate (Plain Reader Pete)**: You probably don't need to contribute proofs directly. The phase completion and audit documents are written for you. If you have zero prior with proof assistants, start with `docs/pythagoras-for-beginners.v`. If you find a gap between a proof and real NTS/JTS behaviour, open an issue with a minimal reproducer.

## Process expectations

- **New theorems** must:
  - Compile under stock Rocq 9.x (the pinned versions in the Dockerfile / `development-environment.md`).
  - Terminate with `Qed.` (or `Defined.`).
  - Depend only on Stdlib (for `theories/`) or Flocq 4.2.x (for `theories-flocq/`).
  - Carry a header comment naming the corresponding NTS module or JTS algorithm.
  - Include the SPDX licence header and AI-assistance disclosure (copy the pattern from existing files).

- **Sessions and design work** (especially for deep contributors and AI agents) follow the patterns documented in the Reading Guide under Scrum-Master Sara and Tech-Lead Tess:
  - Grep first.
  - Red phase: state the simplest target + predicted tangents.
  - Green phase: attempt deliverables, stop at the first genuine tangent.
  - Refactor phase: run the full gauntlet (`check_admitted.sh`, `audit_axioms.sh`, `check_readme_axioms.sh`).
  - Explicit stopping conditions.
  - Outcome documents record what landed / collapsed / remains, with branch info.

- **Pruning and "less dumb" maintenance** is ongoing. The actor filter ("is this useful for at least one of the defined actor roles per their documented path?") plus the stop condition ("after a full git log scan, do we have to put back >10% of the batch?") govern moves to `docs/history/`. Joost the BDFL has final authority on borderline cases. See the pruning log in `docs/history/README.md` and the detailed plan in the repo's session plan.md for the exact process.

- **Stacked PRs / cascades**: Common for multi-session engagements. Review the bottom PR first; the rest inherit its content.

- **AI assistance**: Disclose it (the existing files set the pattern). The session workflow in the Reading Guide is the expected shape for agent-driven work.

## Where to ask / review

- Substantive questions: GitHub Issue.
- "Is this PR ready?": Comment on the PR.
- Review cadence is typically same-day for triage, 1-3 days for full review.

The bar is deliberately high, but the discipline is fully documented in the actor Reading Guide and the four registries. The project ships conditional headlines and registered deferred proofs rather than silent stubs.

Welcome. Pick your card in `docs/HELP.md` and contribute accordingly. Joost mag het weten.