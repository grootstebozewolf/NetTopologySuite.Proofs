# Map — An MMF release bar for the opam packages

Charted 2026-08-24 · Tickets: [`docs/scout/tickets-opam-mmf/`](tickets-opam-mmf/README.md)

## Destination

A **locked release bar** — a named checklist plus the gate evidence it cites, on a
pinned corpus commit — which, when met, makes **`rocq-spatial-algebra 0.1.0`**
and **`rocq-robust-predicates 0.1.0`** *installable from the Rocq opam
archive*. The map is done
when nothing remains to decide before someone can write that bar and clear it.

This map does **not** cut the releases. Plan, don't mint.

## Notes

- **Domain:** [`CONTEXT.md`](../../CONTEXT.md). Consult it before naming anything;
  add terms there as they settle.
- **These are Rocq libraries, not OCaml libraries.** Both packages ship `.v`
  files under the `NTS.Proofs` logpath and depend on `rocq-core` / `rocq-stdlib`
  / `coq-flocq`. Neither contains a line of OCaml. "The OCaml libraries" means
  "the things we distribute through opam" and is a phrase to retire.
- **MMF is imported vocabulary.** The term appears nowhere in this repo; it comes
  from the `grootstebozewolf/jts` fork (`doc/MMF_OPTION_B.md`). We import its
  *shape* — a named checklist plus published gate evidence on a pinned mint — and
  define an **opam-specific** bar. The fork's own gates (TestBuilder queue, UX
  SIGN, laser ratchet) have no analogue here and are not inherited.
- **Skills:** `/grilling` and `/domain-modeling` on decision tickets. Research
  tickets need a `/research` session.
- **Standing preferences:** gates over prose — a claim that lives only in a
  comment has already failed once here. Optimise for maintainability →
  soundness → performance. Cite by name, never by line number.
- **Tracker:** this map and its tickets are tracked markdown under `docs/scout/`,
  matching [the epic-block map](map-epic-block-64-69.md). One ticket per session;
  claim by adding `**Claimed:** <name>` under the title before doing any work.

### Settled while charting (do not re-litigate)

- **The bar requires opam-installable.** A GitHub release with an attached
  tarball is not a mint. An MMF nobody can `opam install` has no "M".
- **Both packages are `rocq-*` and restart at 0.1.0.** Settled by ticket 01 —
  no objection upstream, nothing was ever released to the archive, so there is
  no lineage to continue. Supersedes the original 0.1.4 / 0.1.3 targets.
- **The manifest stays pinned.** Same module set, updated content — that is what
  a `0.1.x` patch means here. Growing the packages is a separate effort.
- **Manifest closure is part of the bar, and gated.** Not a nice-to-have.
- **Mint before the module split.** A split renames files and changes package
  contents materially; ship the current known-good set first.

### Findings that seeded this map (verified 2026-08-24)

No archive mint (GitHub tarballs only). Manifest-closure claim is
comment-only and stale. `OPAM_PUBLISH_TOKEN` never reached the
archive. Declared `rocq-core {>= "9.0"}` is untested (CI is 9.2.0).
`DE9IM.v` has changed since the last tarball. Detail lives on the
closed tickets below.

## Decisions so far

- [Collect the community verdict on the `rocq-*` rename](tickets-opam-mmf/closed/01-community-verdict-on-rocq-rename.md)
  — both `rocq-*`, restart at **0.1.0**.
- [Decide the Rocq version constraint](tickets-opam-mmf/closed/03-rocq-version-constraint.md)
  — `rocq-core {>= "9.2" & < "9.3~"}`; `coq-flocq {>= "4.2.2" & < "4.3~"}`.

## Not yet specified

- **What verifies "installable".** A consumer smoke test — fresh switch,
  `opam install`, `Require Import NTS.Proofs.DE9IM` — is the obvious shape, but
  it cannot be specified until ticket 04 establishes how publishing actually
  behaves here.
- **Whether the bar requires a per-package CHANGELOG.** None exists anywhere
  today; six releases have shipped without one.
- **The external-consumer doc surface**, particularly for
  `robust-predicates`, whose selling point includes machine-checked
  counterexamples to a textbook theorem. What a stranger needs in order to trust
  and use that is not yet a sharp question.
- **Lockstep or independent release.** The two packages have always been tagged
  minutes apart, but nothing says they must move together — and their bars will
  differ on the axiom line.
- **Whether the `NTS.Proofs` logpath is right for a distributed package.** Both
  packages install into the corpus's own namespace; whether that is
  neighbourly in a shared opam namespace is unexamined.

## Out of scope

- **Packaging the `oracle/` OCaml as an opam library.** Real OCaml exists
  (`driver.ml`, `extracted.ml`, `nts_ffi.ml`, `relate_matrix.ml`) and is
  entirely unpackaged, but this map is about the two existing Rocq packages. A
  separate effort if it is ever wanted.
- **The module split of `Orient_b64_exact.v`** and the release it will drive.
  Sequenced explicitly after this mint.
- **Growing either package's module set.** Follows from the pinned-manifest
  decision.
- **The jts fork's MMF gates.** Named here only to record that they are
  deliberately not inherited.
