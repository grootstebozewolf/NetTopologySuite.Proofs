# Contributing to NetTopologySuite.HoTT

Thank you for your interest in contributing to the HoTT-based formalisation that links Rocq/Coq models of NetTopologySuite / JTS geometry and topology algorithms to the C# implementation.

**Context of the pivot.** The previous classical-reals corpus (the "Froq" / NetTopologySuite.Proofs body of >1,100 Qed theorems, phases, audits, oracles, and build) has been archived under `archive/`. See [`archive/README.md`](archive/README.md) and the new top-level [`README.md`](README.md). We are changing the formal substrate to Homotopy Type Theory to obtain a cleaner story for *equivalence* between the formal specification and the C# code (via univalence, path transport, synthetic topology, etc.).

**Axiom policy (HoTT era):** One axiom allowed — let's be generous (see the "Axiom policy (HoTT era)" section in the root `README.md` for the full friendly wording).

**The spirit of the rule remains:**

> New theorems and equivalence proofs end with `Qed.` (or `Defined.` for computable terms).  
> Bare `admit` (or extra axioms beyond the one generous allowance) still needs explicit, documented justification.  
> Nothing is silently stubbed.

The [Reading Guide](docs/READING-GUIDE.md) and friendly [Help cards](docs/HELP.md) define the consolidated actor roles (preserved from the prior era, lightly adapted). Use them to orient yourself. The roles (Newbie Nate, Scholar Sam, Tech-Lead Tess, Joost the BDFL, Consumer Connie, NTS-Upstream Norm, etc.) are still the primary way we decide what counts as useful progress.

## Quick start for different contributor types

See your role in [docs/HELP.md](docs/HELP.md) (or the full [docs/READING-GUIDE.md](docs/READING-GUIDE.md)):

- **Newbie Nate (incl. Rocq Rookie Ray / Plain Reader Pete)**: Start with the top of `README.md` (the pivot statement). If you have literally never used a proof assistant, open `docs/pythagoras-for-beginners.v` first and step through it. The smallest first contributions will likely be re-proving (or transporting) a well-understood classical lemma in HoTT style, or writing a tiny equivalence sketch.

- **Tech-Lead Tess / Project Meta (Pat/Sara)**: Work from the new HoTT roadmap in `README.md`, the archived retros and proof-structure documents under `archive/docs/` (especially the conditional-headline + named-hypothesis pattern and the JCT/vacuity findings — these are still conceptually relevant), and the session workflow in `docs/FOR-AI-AGENTS.md`. Two-route design and explicit stopping conditions remain valuable.

- **Scholar Sam (incl. Auditor Avery)**: The archived corpus + the new HoTT methodology. Pay special attention to how we use (or avoid) univalence, how we state equivalences to C# types/algorithms, and whether the transport lemmas actually deliver on the "linking" promise.

- **Quality Gatekeeper (Max/Ruby / CI / Risk roles)**: Review new HoTT work against the "one axiom, let's be generous" policy (`docs/axiom-policy.md` + root README). When classical material is touched, the archived guardrails in `archive/scripts/` still apply. Core invariant across both: no quiet stubs, explicit justification for `admit` or extra axioms.

- **Consumer Connie / NTS-Upstream Norm**: You care about the *linkage* artefacts — the equivalence proofs, transport lemmas, or verified oracles that let NTS C# call (or be compared against) the formal model. The HoTT era's goal is precisely to make that link first-class rather than "the oracle matches on these test vectors."

- **Joost the BDFL (Joost mag het weten)**: You already know (or will quickly form) the complete picture. You have final say on scope for the pivot, what constitutes useful HoTT + C# correspondence work, what stays at top-level `docs/` vs. future `hott-history/`, and tie-breakers. Your path legitimately includes the entire `archive/`.

- **GIS Gus / BIM Bea**: The phase completion documents are now in `archive/docs/`. For the HoTT era, the relevant cards will evolve to describe which topological invariants have been given synthetic or univalent treatments and how they relate to real NTS behaviour (especially arcs/CIRCULARSTRING).

## Process expectations (transitional — HoTT era)

- **New sources** (under future `theories-hott/`, `equivalences/`, etc.) must:
  - Be stated in a HoTT style (using the HoTT library or an agreed homotopy layer).
  - Terminate with `Qed.` (or `Defined.`).
  - Carry clear headers naming the corresponding NTS C# module(s) or JTS algorithm + (if an axiom is used) the justification for the single allowed axiom per the root README policy.
  - Include SPDX + AI-assistance disclosure (same pattern as before).
  - For linkage work: include (or clearly scope) the equivalence/ transport statement that connects the Coq model to the C# side.

- **Sessions and design work** (especially AI agents) follow the patterns documented in the (preserved) [`docs/FOR-AI-AGENTS.md`](docs/FOR-AI-AGENTS.md) and the archived session retros:
  - Grep first (including the archive when relevant).
  - Red phase: simplest target + predicted tangents + explicit stopping conditions.
  - Green: attempt, stop at genuine tangent.
  - Refactor: clean up, update any new registries or equivalence docs.
  - Outcome documents (prompt + result) are still expected for non-trivial work.

- **Pruning / archiving** continues to be governed by the actor filter ("useful for at least one defined persona per their path?") + stop condition. The old `docs/history/` pruning log is itself now archived; new HoTT work will generate its own history under `docs/` or a HoTT-specific subtree.

- **Stacked PRs / cascades**: Still common. Review bottom-up.

- **AI assistance**: Disclose it. The Red/Green/Refactor shape remains the expected workflow.

## Where the classical corpus still matters

The archive is not a trash can — it is the reference implementation of many of the lemmas we will want to re-express (or transport) under HoTT. When a classical proof already exists for a fact, the HoTT version should cite it (by archive path + theorem name + git SHA at archive time) and explain the relationship (re-proof, synthetic version, transport via some equivalence, etc.).

## Where to ask / review

- Substantive questions: GitHub Issue.
- "Is this PR ready?": Comment on the PR.
- Review cadence is typically same-day for triage, 1-3 days for full review.

The bar remains deliberately high. The project will ship *equivalences and transport* rather than only classical Qed-closed conditionals.

Welcome to the HoTT chapter. Pick your card in `docs/HELP.md` and contribute accordingly. Joost mag het weten.
