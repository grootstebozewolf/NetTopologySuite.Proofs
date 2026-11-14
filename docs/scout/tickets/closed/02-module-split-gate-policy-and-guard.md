<!-- doc-kind: finding
date: 2026-08-22
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Write the module-split gate: policy and ratchet guard

**Type:** task · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** —

## Question

The split criterion decided for this effort exists nowhere in the repo: there is
no size policy, no threshold, and no CI size check (`make ci-guards` runs five
guards — admitted, README axioms, deferred registry, claims, oracle handrolled —
none measures size). Write it down and enforce it.

Deliverables:

1. **Policy**, in `docs/macro-meso-micro.md` beside the meso scale it belongs to:
   a module over **1234 lines** whose `(transitive dependents + 1) × lines`
   reaches **3210** must be split, via the established umbrella pattern (original
   name kept as a `Require Export` umbrella, byte-identical declaration set,
   `Print Assumptions` footers carried verbatim).
2. **Guard**, wired into `make ci-guards`: computes the metric over `theories/`
   and `theories-flocq/`, compares against a **shrink-only allowlist** carrying
   headroom so a comment-sized edit to a listed module does not fail the build.
   Fails when an unlisted module crosses the gate, or a listed one grows past its
   headroom. The allowlist may never gain an entry.
3. **The seed protocol**: one split per session, drawn from the queue by the day's
   seed (e.g. `20260822`), recorded the way
   `docs/geos-open-issues-triage-2026-08.md` records its sample seed.

Open question for the ticket: what headroom figure? A fixed pad (+50 lines) is
predictable; a percentage (+5%) scales with the monolith. Pick one and say why in
the policy text.

Reference computation (2026-08-22): gated = `Orient_b64_exact.v` 1270×72,
`HotPixel_b64.v` 2604×32, `Route2.v` 2293×9; exempt near-miss =
`ArcLineIntersect_b64_exact.v` 1516×2 = 3032.

## Resolution

**Closed 2026-08-22. The gate is written down, enforced, and its two failure
modes are demonstrated.**

Delivered:

1. **Policy** — `docs/macro-meso-micro.md`, new *Module split gate* subsection
   under Meso (where the module *is* the audit unit). States both conditions, why
   the line floor is load-bearing, the umbrella pattern, the ratchet, and the
   seeded chore.
2. **Guard** — `scripts/check_module_split.py`, wired into `make ci-guards` after
   the existing `python3` guard. Modes: default (enforce), `--list` (queue, plus
   the monoliths-below-gate and 800..1233 watch bands), `--all` (full table).
   Exit codes follow house style: 0 holds, 1 violation, 2 usage/file error.
3. **Allowlist** — `docs/module-split-allowlist.txt`, three entries recorded with
   the reasoning that should survive into whoever picks up the chore, including
   the note that `HotPixel_b64.v`'s "split BLOCKED — 21 reverse deps" verdict
   predates the umbrella pattern and deserves revisiting rather than inheriting.
4. **Seed protocol** — documented in both the policy and the allowlist header.

**Headroom decided: 5 % of the recorded line count, rounded up** (131 lines for
`HotPixel_b64.v`, 64 for `Orient_b64_exact.v`). Chosen over a fixed pad because
the file most likely to need slack mid-split is the biggest one, and a percentage
gives it proportionally more; a fixed +50 would be generous to a 1270-line module
and stingy to a 2604-line one.

**A design correction the ticket did not anticipate.** The allowlist records
**lines, not the metric**. Blast radius rises whenever some *other* module starts
requiring a listed one, so gating a listed module on its metric would fail a
contributor's build for an edit they did not make. The guard therefore compares
lines-with-headroom for listed modules, and applies the full gate only to
unlisted ones.

**Stale entries fail too.** A listed module that no longer trips the gate is a
build failure, so the entry must be deleted by the change that splits it. Without
this the list would silently accumulate fossils and stop being a ratchet.

**Both failure modes exercised** before wiring (allowlist restored afterwards):
dropping the `Route2.v` entry produced `NEW VIOLATION … 2293 lines x9 = 20637 >=
3210` with exit 1; adding a `theories/Distance.v` entry produced `STALE ENTRY …
no longer trips the gate` with exit 1; the restored tree reports *gate holds: 3
gated module(s), all 3 allowlisted and within headroom*, exit 0.

**Superseded** `docs/scout/split-metric.py`, deleted here: the guard's `--list`
mode is the same computation with one implementation instead of two.
