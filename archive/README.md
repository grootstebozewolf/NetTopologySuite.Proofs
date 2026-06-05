# Archive of NetTopologySuite.Proofs (Froq era)

This directory contains the archived classical-reals proof corpus, companion documents, build infrastructure, oracle extraction, and session history from the pre-HoTT phase of the project (formerly known internally as "Froq").

## What was moved here

- `theories/` — Stdlib-only Rocq modules (foundational geometry over classical reals)
- `theories-flocq/` — Flocq-dependent modules (binary64 instances, extraction oracles)
- `oracle/` — OCaml drivers, test generators, hand-rolled vs extracted comparison
- `scripts/` — CI guardrails (check_admitted, axiom audit, etc.)
- `_CoqProject*` — project files for rocq makefile
- `docs/` — all phase completion, audit, proof-structure, retro, seam-map, and detailed history documents (the "companion documents")
- `Dockerfile`, `.dockerignore`, `.github/workflows/`, `.claude/` — the pinned Rocq+Flocq container build and CI

## Status at archive time

- >1,100 Qed-closed theorems
- 3-axiom discipline (classical reals) in `theories/`
- Registered `Admitted` tiers for counterexamples and deferred proofs
- Phase 0–4 of the NTS topological chokepoint roadmap largely delivered (with precise named gaps)
- Oracle modes shipped to NetTopologySuite.Curve for several predicates

## Why archived

This is a deliberate pivot from the "Froq" (formal Rocq proofs over classical reals + Flocq) approach to **HoTT (Homotopy Type Theory)** as the vehicle for linking formal specifications in Rocq/Coq to the C# implementation in NetTopologySuite.

HoTT provides:
- Synthetic homotopy and higher paths as first-class citizens (natural for topological claims)
- Univalence (equivalences are paths/identities)
- Better tools for transporting structure and proofs along equivalences — a promising fit for "the C# code implements the same math as the Coq model"

The previous corpus remains valuable as reference, counterexample registry, and proof-engineering precedent. All documents are preserved exactly as they were.

## How to explore the archive

See `archive/docs/` for the moved companion documents (phase completion, audit, proof-structure, seam maps, retros) and `archive/docs/history/README.md` + `archive/docs/history/sessions/README.md` for navigation of the full session record and pruning log.

The old root `README.md` *is* copied here as `archive/old-README-Proofs.md` for reference (the live root README has been replaced by the HoTT pivot version). Consult git history for the pre-archive state of any individual file.

## Continuing under HoTT

See the new root [`README.md`](../README.md), [`docs/HELP.md`](../docs/HELP.md) (personas preserved), and [`docs/pythagoras-for-beginners.v`](../docs/pythagoras-for-beginners.v) (the single kept entry-point proof example).

The HoTT work will live in new directories (e.g. `theories-hott/`) once bootstrapped. The personas (Newbie Nate, Scholar Sam, etc.) continue to apply, now oriented around HoTT + C# correspondence rather than classical phase completion.

Joost the BDFL retains final say on scope for the pivot.

---

Archived as part of the "refactor-from-froq-to-hott" effort. The mathematical content and engineering lessons are not discarded — they are the foundation we stand on while changing the formal substrate and the bridging strategy to C#.
