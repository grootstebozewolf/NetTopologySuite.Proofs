<!-- doc-kind: guide -->
# Domain Docs

How the engineering skills should consume this repo's domain documentation when exploring the codebase.

## Before exploring, read these

- **`CONTEXT.md`** at the repo root, or
- **`CONTEXT-MAP.md`** at the repo root if it exists — it points at one `CONTEXT.md` per context. Read each one relevant to the topic.
- **`docs/adr/`** — read ADRs that touch the area you're about to work in. In multi-context repos, also check `src/<context>/docs/adr/` for context-scoped decisions.

If any of these files don't exist, **proceed silently**. Don't flag their absence; don't suggest creating them upfront. The `/domain-modeling` skill (reached via `/grill-with-docs` and `/improve-codebase-architecture`) creates them lazily when terms or decisions actually get resolved.

## File structure

This repo is **single-context**:

```
/
├── CONTEXT.md
├── docs/adr/
│   └── ADR-0001-fresnel-internalisation-stack.md
├── theories/            Rocq proofs (Stdlib reals)
├── theories-flocq/      Rocq proofs (binary64 / Flocq lane)
├── oracle/              extracted oracle + generators
└── tools/, tests/       differential tooling
```

ADR-0001 governs the Fresnel internalisation stack and licence path; it also
carries the layer law that meso-scale audits check (`core → predicates →
overlay → topology/Jordan → arcs → mesh`).

## Use the glossary's vocabulary

When your output names a domain concept (in an issue title, a refactor proposal, a hypothesis, a test name), use the term as defined in `CONTEXT.md`. Don't drift to synonyms the glossary explicitly avoids.

If the concept you need isn't in the glossary yet, that's a signal — either you're inventing language the project doesn't use (reconsider) or there's a real gap (note it for `/domain-modeling`).

## Repo-specific companions to CONTEXT.md

`CONTEXT.md` is the glossary. Two further docs carry structure a skill will want
before proposing work:

- **`docs/macro-meso-micro.md`** — the three work scales: macro (board epics,
  keyed by `topic:`), meso (one `.v` module as the audit unit, `Require` edges as
  the blast cone), micro (`claimId` + `witness`, Red→Green→Refactor).
- **`docs/verified-claims.md`** — the claims register (every cited theorem).
  Check it before asserting something is or isn't proven.

## Flag ADR conflicts

If your output contradicts an existing ADR, surface it explicitly rather than silently overriding:

> _Contradicts ADR-0001 (Fresnel internalisation stack) — but worth reopening because…_
