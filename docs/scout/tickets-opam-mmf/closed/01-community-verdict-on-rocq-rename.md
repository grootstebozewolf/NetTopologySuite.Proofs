<!-- doc-kind: finding
date: 2026-08-24
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Collect the community verdict on the `rocq-*` rename

**Type:** task · **Map:** [An MMF release bar for the opam packages](../../map-opam-mmf-release-bar.md)
**Blocked by:** nothing — takeable

## Question

The rename question is already out with the community. This ticket collects the
verdict and records what follows from it. Nothing here is a fresh decision: the
map settled *rename if nobody objects*.

Find the thread and read it. The likely venue is the Rocq Zulip — the
`#Rocq community devs & users` channel, topic **"Project showcase:
NetTopologySuite.Proofs (JTS/NTS companion)"** — which is also the subject of a
standing request to set up monitoring; that monitor does not exist yet and
reading the thread needs a Zulip credential, so this ticket may have to be
resolved by hand.

Record three things:

1. **The verdict.** Objection, no objection, or no response after a stated
   waiting period. "No response" is a real outcome and needs its own rule — decide
   how long silence counts as consent, and say so.
2. **The resulting names.** Either `rocq-spatial-algebra` /
   `rocq-robust-predicates`, or the `coq-*` names retained. Note that the
   packaging *directories* are already `packaging/rocq-*` while the opam files are
   `coq-*.opam`, so one of the two is wrong either way and the inconsistency gets
   fixed by this ticket's answer.
3. **What happens to the version numbers.** An opam rename is a **new package**,
   not a version bump — a renamed package has no 0.1.3 to succeed. So if the
   rename lands, decide whether the first upstream version is `0.1.4` /
   `0.1.3` (continuing the GitHub-release lineage) or resets. This is the part
   that decides whether "mint 0.1.4" is even the right label, so it is the
   answer the rest of the map waits on.

Also worth capturing while in the thread: any archive-convention guidance for a
Rocq 9 library that bears on the bar — required metadata fields, naming rules,
or `logpath` expectations.

---

## Resolution

**No objection. Both packages rename to `rocq-*`, and versioning restarts at
0.1.0.**

The upstream reply, in substance: *ideally* a `rocq-*` package should depend only
on other `rocq-*` packages — including `rocq-core` rather than `coq-core` — so
that CI can prove it builds without the Coq compatibility binaries. But in
practice not all packages follow that rule, so pick the name that best fits the
development. Distribution is by opening a pull request on
`https://github.com/rocq-prover/opam`, and we were encouraged to do so.

### What follows

1. **Names:** `rocq-spatial-algebra` and `rocq-robust-predicates`.

   The ideal rule initially suggested an asymmetry — `spatial-algebra` depends
   only on `rocq-core` and `rocq-stdlib` and so satisfies it outright, while
   `robust-predicates` depends on **`coq-flocq`** and `rocq-flocq` does not
   exist. That asymmetry was **dropped deliberately**: the rule is not
   universally followed, the name should suit the development, and Flocq 4.2.2
   already implements the Rocq standard library — so the dependency is
   Rocq-native in substance and only the upstream *name* is still `coq-*`. Both
   packages therefore take `rocq-*`, and the reasoning is recorded in the
   `coq-flocq` dependency comment so nobody reads it as an oversight.

2. **Versions restart at 0.1.0.** Nothing was ever released to the archive, so
   there is no lineage to continue and no consumer to break — the cheapest
   possible moment to renumber. This supersedes the map's target of
   "spatial-algebra 0.1.4 / robust-predicates 0.1.3": under a new package name
   those numbers would have claimed a history the archive never saw.

3. **New tag prefix, out of necessity.** `spatial-algebra-v0.1.0` and
   `robust-predicates-v0.1.0` **already exist** as tags from June, so restarting
   at 0.1.0 under the old scheme would collide. Tags are now
   `rocq-spatial-algebra-v0.1.0` and `rocq-robust-predicates-v0.1.0`, and the
   workflows' prefix-stripping and release filters were updated to match.

4. **The old releases stay.** Six GitHub releases under the `coq-*` names remain
   as history; nothing is deleted. Since none ever reached the archive, there is
   nothing to deprecate upstream and no redirect to arrange.

5. **`>= 4.2.2` on Flocq is now principled rather than empirical.** It is the
   first Flocq implementing the Rocq standard library; anything older reintroduces
   the Coq compat layer and defeats the naming.

### Verified after the rename

Both packages assemble, build and lint under the new names — `rocq-spatial-algebra`
2 files, `rocq-robust-predicates` 21 files, `make` clean and `opam lint` *Passed*
for each, on Rocq 9.1.1 + Flocq 4.2.2. The `theories/dune` `(package ...)` fields
were updated in step with the opam filenames, which is what dune resolves against.

### Carried forward

- **Ticket 04 matters more, not less.** The automated `opam publish` path has
  failed silently six times. For this first `rocq-*` mint the reliable route is
  the one upstream described — open the archive pull request by hand — which
  sidesteps the broken automation rather than depending on it.
- **The map's Destination wording is now stale**, naming 0.1.4 and 0.1.3. It
  should read 0.1.0 for both.
