# Getting Started

Welcome to **NetTopologySuite.Proofs**.

This repository contains mechanically verified Rocq proofs of foundational properties used by NetTopologySuite (the .NET port of JTS Topology Suite).

**The single most important rule:**

> Every theorem ends with `Qed.` (or `Defined.`).  
> No `Axiom`, no `Parameter`, no bare `admit.` in the `.v` files.  
> The only exceptions are six explicitly registered `Admitted` entries with documented justification.

## First 60 seconds

1. Run this in the repo root:

   ```sh
   make help
   ```

   (It works even if you have no Rocq installed.)

2. Open the friendly role cards:

   ```sh
   cat docs/HELP.md
   ```

   Find the card that matches you (or the closest one). Each card gives you a concrete "OPEN" action and a realistic time estimate.

3. For the complete map of every role and their recommended reading paths, see:

   [`docs/READING-GUIDE.md`](docs/READING-GUIDE.md)

## Common on-ramps

- **I have literally never used a proof assistant before** — Open [`docs/pythagoras-for-beginners.v`](docs/pythagoras-for-beginners.v) in CoqIDE or VS Code + VSCoq/Coq extension and step through it. It is deliberately self-contained and heavily commented.
- **I just want the headline** — Read the first three paragraphs of `README.md`.
- **I use NTS / JTS and want to know what is proved** — Follow the GIS Gus or NTS-Upstream Norm / Consumer Connie card in `docs/HELP.md`.
- **I care about circular arcs / CIRCULARSTRING** — Follow the BIM Bea card.
- **I want to build the proofs locally** — See `docs/development-environment.md` (container is canonical; host fallback documented).
- **I want to contribute (or run an AI coding session)** — Read `CONTRIBUTING.md` + [`docs/FOR-AI-AGENTS.md`](docs/FOR-AI-AGENTS.md) + the relevant sections of the Reading Guide for session workflow and invariants.
- **I maintain or review this corpus** — Start with the four registry files in `docs/` (`admitted-*.txt`, `axiom-allowlist.txt`, `audit-exceptions.txt`).

## Quick build notes

- The easy foundational layer (`theories/`) builds with stock Rocq 9.1.1 (no Flocq needed) via `make host`.
- The full corpus (including binary64 proofs under Flocq) is normally built inside the pinned container described in the `Dockerfile`.
- All CI guardrails (`check_admitted.sh`, axiom audit, etc.) are runnable locally once you have a build.

## Where the real work lives

Most development happens via long, structured sessions whose outputs (prompts, outcomes, retros) are recorded in `docs/`. The Reading Guide and the "Help — pick your path" cards exist precisely so you can find the relevant historical context quickly instead of drowning in the archive.

Pick your card in `docs/HELP.md` and go.

The project is deliberately rigorous. The onboarding surface is now deliberately welcoming. Both can be true at the same time.

---

Next step: `cat docs/HELP.md` (or just `make help` again).