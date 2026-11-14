<!-- doc-kind: guide -->
# Macro · Meso · Micro

**Status:** living paradigm for NetTopologySuite.Proofs  
**Audience:** humans, auditors, RGR agents

The corpus is too large to maintain as a flat list of theorems. Work is organised
on **three scales**. The observatory dashboard
([GitHub Pages](https://merkatorbv.github.io/NetTopologySuite.Proofs/))
surfaces the same stack.

## Macro — domains & epics

| Idea | Examples |
|------|----------|
| Board epic | Retired block **#64–#68**; tracker **#69** is owner-retire ready ([`docs/scout/69-closing-summary.md`](scout/69-closing-summary.md)). Standing epics (**#410** koc, **#423** metric, **#424** hull, **#425** coverage, **#814** / **#1200** core mirrors) stand alone — full wire table in [`TRIAGE_NTS_JTS_ISSUES.md`](../TRIAGE_NTS_JTS_ISSUES.md) §Wire map |
| Topic tag | `topic: core`, `buffer`, `precision`, `relate`, `mesh`, `koc`, `metric`, `coverage`, `hull`, … |
| Role | Human-scale “where does this live?” and blast-cone epicenter |

Macro answers: *which geometry family / open issue owns this work?*

## Meso — modules

| Idea | Examples |
|------|----------|
| Atom | A `.v` module (not 5 000 free-floating statements) |
| Graph | `Require` edges; blast cone = module + dependents |
| Layer law | core → predicates → **overlay** → topology (Jordan) → arcs → mesh |
| ADR-0001 | Jordan **needs** Overlay; circular Require is a tripwire; prefer **rocq makefile** / `_CoqProject` |

Meso answers: *which file is the audit unit, and what does a change irradiate?*

Smoke without the full chain: self-contained tripwire files that duplicate
already-Qed leaves (e.g. ring lemmas, `inCircle_R`) and `Require` only a thin
witness module — mark with `(* ADR-0001: self-contained smoke *)`.

### Module split gate

Modules are the architectural seams; keep them small enough and the optimisation
becomes natural. The gate is **derived, not judged** — a module must be split
when **both** hold:

| Condition | Value |
|-----------|-------|
| Monolith | `lines ≥ 1234` |
| Load-bearing | `(transitive dependents + 1) × lines ≥ 3210` |

The line floor carries real weight: the blast-weighted product *alone* selects
**foundational** modules rather than **giant** ones. `theories/Distance.v` is 402
lines with 455 transitive dependents (product 182 910) and has no size problem
whatsoever; without the floor, 180 of 536 modules would be "gated", 169 of them
under 800 lines. Above the floor, the product orders the queue.

**Splits use the umbrella pattern**, as established by #464 / #465 / #472 / #475:
the original name stays as a `Require Export` umbrella, the declaration set is
byte-identical (name-for-name), and `Print Assumptions` footers move verbatim to
each declaration's new home. Importers therefore cannot observe a split, so
**high fan-in is not a reason to refuse one** — it is a reason to sequence it
carefully.

**Clique facades** (PR #534, `JordanRingKit.v`; `JctSeamPack.v`) are the other
Require-Export shape: a *new* name that packs modules already co-required
together (support ≥ 12). Savings = importers × (members − 1). Not a monolith
split — no declarations move. Overlay stays a member of the kit, not a
Require of Jordan (ADR-0001 layer law). RelateNG and Overlay-only leaves
stay off both facades. One pack per clique — no `JctSeamPack7` twin.

**Enforcement is a ratchet.** `scripts/check_module_split.py` runs in
`make ci-guards`; modules already over the gate are recorded in
[`docs/module-split-allowlist.txt`](module-split-allowlist.txt) with their line
count, plus 5 % headroom so a comment-sized edit does not fail the build. The
list may **shrink, never grow**: a newly gated module is a build failure, and a
listed module that no longer trips the gate is *also* a failure, so the entry
must be deleted by the change that splits it. The recorded figure is lines rather
than the metric on purpose — blast radius rises when some *other* module starts
requiring yours, and that must not fail your build.

**Working the queue** is a maintainer's chore: one split per session, drawn from
`python3 scripts/check_module_split.py --list` by the day's seed (e.g.
`20260822`) — the same seeded-sample convention as
[`geos-open-issues-triage-2026-08.md`](geos-open-issues-triage-2026-08.md).
Recording the seed is what stops the cheap ones being taken first forever.

## Micro — claims & witnesses

| Idea | Examples |
|------|----------|
| Claim key | Board subtask `claimId: 68-a` or teaching seed `even-square` |
| Witness | `witness: empty-circle`, `(* WITNESS {"claimId":"…"} *)` |
| Loop | **Red** (failing surface) → **Green** (Qed + CI) → **Refactor** (merge or next rung) |
| Eval | Micro-kernel / Rocq: Eval → Qed; mutation suite probes vacuity |
| Registry | Dynamic micro claims: board sync + register + auto-WITNESS |

Micro answers: *what is the smallest falsifiable obligation right now?*

## Machine header (PR bodies)

```text
topic: mesh
claimId: 68-a
witness: empty-circle
```

| Tag | Scale | Skip form |
|-----|-------|-----------|
| `topic:` | macro | `topic: none` |
| `claimId:` | micro (board or seed) | `claimId: none` |
| `witness:` | micro falsifier | `witness: none` |

## Why three scales

1. **Auditors** sample modules (meso), not every lemma.
2. **Agents** plan RGR on claimIds (micro) without loading the whole corpus.
3. **Humans** track open geometry programs via epics (macro).
4. **CI / review** attach blast cones, ADR-0001 dep checks, and mutation only
   when the right scale is named.

## Related

- `docs/adr/` (dependency order, witness tags) when present in-tree  
- `docs/verified-claims.md` — cited theorem ledger (meso/micro evidence)  
- `TRIAGE_NTS_JTS_ISSUES.md` — macro issue map  
- Observatory generator: `scripts/gen_dashboard.py`
