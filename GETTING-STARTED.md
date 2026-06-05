# Getting Started (HoTT pivot)

Welcome to **NetTopologySuite.HoTT**.

This repository is the home for formal Coq/Rocq work (now pivoting to Homotopy Type Theory) that links the mathematical model of NetTopologySuite's core geometry and topology algorithms to the C# implementation.

**The prior classical proof corpus ("Froq" / NetTopologySuite.Proofs) has been archived.** See [`archive/README.md`](archive/README.md). The welcoming surface, the personas, and the single beginner proof example have been kept.

**The single most important ongoing rule (adapted):**

> New work ends with `Qed.` (or `Defined.`).  
> No bare `admit`, `Axiom`, or `Parameter` in the formal sources without explicit registry/justification.  
> The HoTT era will evolve the exact discipline, but the spirit of "nothing quietly stubbed" remains.

## First 60 seconds

1. Pick your persona:

   ```sh
   cat docs/HELP.md
   ```

2. Read the current HoTT-era axiom policy (one axiom allowed — we're being generous):

   ```sh
   cat docs/axiom-policy.md
   ```

3. For the complete map of roles and recommended paths (now oriented around HoTT + C# linkage):

   ```sh
   cat docs/READING-GUIDE.md
   ```

4. If you have literally never used a proof assistant:

   Open [`docs/pythagoras-for-beginners.v`](docs/pythagoras-for-beginners.v) in CoqIDE or VS Code + VSCoq and step through it. It is deliberately self-contained.

## Common on-ramps (HoTT era)

- **I have literally never used a proof assistant before** — [`docs/pythagoras-for-beginners.v`](docs/pythagoras-for-beginners.v) (step through it; heavily commented "hello world" that proves Pythagoras and explains the cost of certainty).
- **I just want the headline** — Read the top of [`README.md`](README.md) (the pivot notice and HoTT motivation).
- **I use NTS / JTS and want to know the story** — GIS Gus or NTS-Upstream Norm card in `docs/HELP.md`.
- **I care about rigorous linkage to C#** — Consumer Connie + the new equivalence / transport focus (see HoTT roadmap in README).
- **I want to contribute (or run an AI coding session)** — [`CONTRIBUTING.md`](CONTRIBUTING.md) + [`docs/FOR-AI-AGENTS.md`](docs/FOR-AI-AGENTS.md) (the session workflow and invariants are still relevant; outputs are now HoTT modules + C# correspondence artefacts).
- **I want the deep history** — `archive/` (old phases, audits, 100+ session retros, the full classical corpus).

## Build / environment notes (transitional)

The old `make help`, host build, containerised Flocq build, and all guardrail scripts live in `archive/`.

- The `pythagoras-for-beginners.v` example only needs a working Rocq installation (any recent version is fine; it uses only `Stdlib.Reals` and `Lra`).
- A fresh HoTT-oriented setup (coq-hott or equivalent + custom layers) and `make` targets will be added once the first modules are created.
- For exploring the archived classical work, see `archive/README.md` (it describes the old container + `_CoqProject.full` path).

## Where the real work will live

Development will continue via structured sessions (Red / Green / Refactor, explicit stopping conditions, two-route designs when the approach is uncertain). Outcomes will be recorded under `docs/` or a future `docs/hott-history/`.

The personas (preserved from the previous era) tell you exactly which documents matter to your role.

Pick your card in `docs/HELP.md` and go.

The project remains deliberately rigorous. The onboarding surface remains deliberately welcoming. Both can be true at the same time — now with paths and univalence in the picture.

---

Next step: `cat docs/HELP.md`.
