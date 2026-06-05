# NetTopologySuite.HoTT

[![HoTT pivot](https://img.shields.io/badge/pivot-HoTT-blue)](https://github.com/grootstebozewolf/NetTopologySuite.Proofs)

Formal specifications and proofs, in Rocq/Coq, of the core geometric and topological invariants used by [NetTopologySuite](https://github.com/NetTopologySuite/NetTopologySuite) (the .NET port of JTS), with a deliberate pivot to **Homotopy Type Theory (HoTT)** as the foundation for linking the formal model to the C# implementation.

> **This is a pivot from the previous "Froq" (classical-reals + Flocq proof corpus) to HoTT.**
>
> The entire prior body of >1,100 Qed-closed theorems, the Phase 0–4 chokepoint work, Flocq binary64 instances, oracle extraction, and all companion audit/proof-structure/retro documents have been **archived** under [`archive/`](archive/).
> See [`archive/README.md`](archive/README.md) and [`archive/old-README-Proofs.md`](archive/old-README-Proofs.md) for the historical record.

**The single kept entry point for formal proof newcomers** is the heavily-commented, self-contained beginner example:

> [`docs/pythagoras-for-beginners.v`](docs/pythagoras-for-beginners.v)

Step through it in CoqIDE / VS Code + VSCoq. It proves the Pythagorean theorem from first principles over the reals and explains why even "obvious" geometry requires real machine effort once everything must be checked. After this file you will understand the spirit of the work — now re-grounded in HoTT.

**Personas / actor roles are preserved.** Find your card in [`docs/HELP.md`](docs/HELP.md). The full reading map (updated for the HoTT era) is in [`docs/READING-GUIDE.md`](docs/READING-GUIDE.md). The roles (Newbie Nate / Rocq Rookie Ray, GIS Gus, BIM Bea, Scholar Sam, Tech-Lead Tess, Joost the BDFL, Consumer Connie, NTS-Upstream Norm, Quality Gatekeeper, etc.) continue to guide contribution and navigation. They now orient around HoTT formalisation + C# correspondence rather than the old classical phase milestones.

---

## Why HoTT for NTS?

Classical set-theoretic / type-theoretic models in Coq (using `R` from the standard library + axioms for classical reals) have already delivered substantial verified results for orientation, intersection, snap-rounding foundations, overlay, and chord-approximated arcs (see the archived corpus).

HoTT offers a different substrate:

- **Paths are data.** In HoTT, equalities are paths; higher paths give structure on equalities. This is native for topology and for "continuous" geometric claims (the JCT seam work in the archive already gestured at continuous paths).
- **Univalence.** Equivalences (`A ≃ B`) are themselves paths (`A = B`). This gives a principled way to transport theorems, proofs, and structure along "the C# implementation is equivalent to the formal model."
- **Synthetic homotopy & higher inductive types.** Many topological invariants (Jordan curve, winding, components, interiors) have synthetic characterisations that avoid point-set bookkeeping.
- **Better extraction / correspondence story.** Rather than only extracting executable code, HoTT emphasises *equivalence* — we can prove that the C# type/algorithm is (homotopy) equivalent to the Coq specification and transport properties across the equivalence.

The long-term goal is a clean, maintainable HoTT formalisation of the load-bearing NTS primitives (robust predicates, noding, overlay topology, curve handling) together with *explicit equivalence proofs* (or transport lemmas) that let us relate the C# `NetTopologySuite.*` implementations back to the formal statements. This is the "linking the formal Coq to the C# code using HoTT" mandate of the current pivot.

The archived classical proofs remain the engineering precedent and the source of many concrete lemmas we will want to re-prove (or transport) in the HoTT setting.

## Current state (post-pivot skeleton)

- The historical proof corpus is fully archived (see `archive/`).
- The welcoming on-ramp (`pythagoras-for-beginners.v`) and the persona/role system (`HELP.md`, `READING-GUIDE.md`, `FOR-AI-AGENTS.md`) have been kept and will be evolved for HoTT + C# work.
- First HoTT sources + RGR planning have landed in `theories-hott/` and `docs/`. See `theories-hott/VoronoiEquivalence.v` (pilot small equivalence for NTS Voronoi link) + `docs/hott-rgr-risk-cost-pivot.md` (strategy) and `docs/hott-rgr-tin-hobby-shewchuk-curve-pivot.md` (next big chunk: TIN/linearise, Hobby, Shewchuk, Curve — chunked small equivs in recommended order, re-use archive via transport). `_CoqProject.hott` for builds.
- A full HoTT-oriented build story will evolve with more modules. All prior classical CI/build/oracle live in `archive/`.

## Axiom policy (HoTT era)

**One axiom allowed. Let's be generous.**

The archived classical corpus ("Froq" era) was deliberately austere: only the three standard classical-reals axioms from Rocq's stdlib were permitted, every `Print Assumptions` was audited against an allowlist, `Axiom`/`Parameter`/`admit.` were banned outright except for six explicitly registered cases, and CI ran multiple guardrail scripts on every change.

For the HoTT pivot we are changing the trade-off. The goal is a **clean, usable, maintainable formal bridge to the real C# NetTopologySuite code**. Working synthetically with paths, higher inductive types, and univalence has a natural cost in axioms (most commonly the Univalence axiom itself, or a small standard set from the HoTT library).

New rule, deliberately lighter:

- **One load-bearing axiom is allowed** per major piece of HoTT work (typically univalence or the equivalent you actually need to do the C# linkage).
- Document it clearly in the file header: what the axiom is, why it is required for the equivalence/transport story, and what it would take to remove or weaken it.
- The rest of the development must still end in `Qed.` / `Defined.`. No quiet `admit`.
- When working with (or transporting from) material in `archive/`, the old stricter classical rules still apply.
- "Generous" means: we will not recreate the full three-tier admitted registry + per-theorem axiom audit theatre for the HoTT layer unless it becomes necessary. Scholar Sam / Quality roles will review the *justification and the linkage value* of the one axiom instead of counting every assumption.

We are still rigorous where it matters for the C# correspondence. We are just not going to let axiom-counting become the enemy of shipping useful verified linkage.

(If a development genuinely needs a second axiom, talk to Joost the BDFL. "Generous" does not mean "anything goes.")

## Getting started (HoTT era)

1. `cat docs/HELP.md` — pick your persona.
2. If you have never used a proof assistant: open `docs/pythagoras-for-beginners.v` and step through it.
3. Read this README (especially the "Axiom policy (HoTT era)" section) + [`docs/axiom-policy.md`](docs/axiom-policy.md) + [`docs/READING-GUIDE.md`](docs/READING-GUIDE.md).
4. For the deep history of what was already proved classically: `archive/README.md` + the phase/audit files under `archive/docs/`.

See also the (lightly updated) [`GETTING-STARTED.md`](GETTING-STARTED.md) and [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Roadmap (vision)

| Theme                        | Goal                                                                 | HoTT angle                              |
|------------------------------|----------------------------------------------------------------------|-----------------------------------------|
| Synthetic geometry primitives| Re-express orientation, distance, convexity, etc. over HoTT types   | Use HITs for circles, intervals; paths for continuous variation |
| Robust predicates            | Filters + exact cases with soundness                                 | Prove the filter/exact relation as a path or equivalence |
| Topology (JCT, overlay)      | Jordan, bounded components, correct labelling                        | Synthetic JCT; univalent transport of labels |
| C# linkage                   | Explicit correspondence between Coq model and NTS C# types/algos     | `NTS_RobustOrientation ≃ Coq_Orient` + transport of theorems |
| Extraction / FFI             | Where useful, extract; otherwise use verified oracles + equivalence  | Univalence for "the extracted term is the same as the C# port up to homotopy" |
| Arcs & curves                | Native (non-chord) circular primitives                               | S¹ as a HIT; winding numbers as path data |

The archived classical work (especially the conditional-headline + named-hypothesis pattern, the vacuity findings, the Hobby/Halperin formalisation, and the exact binary64 bridges) will be mined for targets and for proof-engineering patterns that still apply.

## Licence

BSD-3-Clause (matching NetTopologySuite).

The archived proofs were derived from NTS / JTS; the new HoTT work will respect the same attribution requirements.

## Contributing under the pivot

The invariants change:

- New theorems will be stated in HoTT style (using the HoTT library or a custom homotopy layer on top of Rocq).
- We still value `Qed.` (or `Defined.`) discipline; bare `admit` is still not allowed without explicit justification. See the "Axiom policy (HoTT era)" section above — one (well-justified) axiom is the new generous default.
- The persona cards still apply — Newbie Nate starts with Pythagoras; Scholar Sam will audit the HoTT methodology and the equivalence claims to C#; Consumer Connie and NTS-Upstream Norm care about the *linkage* artefacts.
- Session workflow (Red/Green/Refactor, explicit stopping conditions, two-route designs) from the archived `FOR-AI-AGENTS.md` and `history/` still serves us; the output artefacts will now be HoTT modules + equivalence proofs rather than classical phase completions. Recent example: `docs/hott-rgr-risk-cost-pivot.md` (RGR analysis of linkage strategy risk/cost).

See [`CONTRIBUTING.md`](CONTRIBUTING.md), [`docs/axiom-policy.md`](docs/axiom-policy.md), and the persona documents for details. Joost the BDFL has final authority on what constitutes useful progress in the HoTT direction.

---

The classical corpus proved an enormous amount about what *can* be verified for NTS geometry. HoTT changes *how* we do it and, crucially, *how we know the C# code is faithful to the verified model*.

Welcome to the HoTT chapter.
