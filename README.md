# NetTopologySuite.Proofs

[![build proofs](https://github.com/MerkatorBV/NetTopologySuite.Proofs/actions/workflows/ci.yml/badge.svg)](https://github.com/MerkatorBV/NetTopologySuite.Proofs/actions/workflows/ci.yml)
[![dashboard](https://github.com/MerkatorBV/NetTopologySuite.Proofs/actions/workflows/pages.yml/badge.svg)](https://github.com/MerkatorBV/NetTopologySuite.Proofs/actions/workflows/pages.yml)

📊 **[Observatory dashboard](https://merkatorbv.github.io/NetTopologySuite.Proofs/)** — a generated status view of the corpus (cited theorems by regime, per-issue verdicts, oracle coverage, trust footprint). Reports only in-repo source of record and deep-links out to [JTS](https://github.com/locationtech/jts) / [NTS](https://github.com/NetTopologySuite/NetTopologySuite); not a JTS/NTS test runner. See [`dashboard/`](dashboard/).

Mechanically-checked proofs of load-bearing geometry facts used by
[NetTopologySuite](https://github.com/NetTopologySuite/NetTopologySuite),
written in [Rocq Prover](https://rocq-prover.org/). Every theorem ends
with `Qed.`, and there are no live `Admitted` theorems. All 12 `Defined.`
in the tree close a `Definition` — decidability procedures that have to
compute — and none of them closes a theorem. This is a proof
corpus, not a verified implementation of NTS.

The corpus enforces a three-axiom allowlist. None of the three is declared
here — all three ship with Rocq's Stdlib, and reach the corpus through its
classical real arithmetic:

```
ClassicalDedekindReals.sig_not_dec
ClassicalDedekindReals.sig_forall_dec
FunctionalExtensionality.functional_extensionality_dep
```

The trio is a **ceiling**, not a floor. A module may rest on fewer:
`Distance.dist_sq_nonneg` uses only `sig_forall_dec` and
`functional_extensionality_dep`, and never `sig_not_dec`. Whatever a module
does rest on is emitted by its own `Print Assumptions` block, so the audit
reads the footprint from the build log rather than from prose.

The ceiling has named exceptions rather than silent ones: 37 files under
`theories/` and 76 files under `theories-flocq/` inherit further axioms
from their dependencies — in the Flocq lane typically
`Classical_Prop.classic`, by way of the binary64 format layer. They are
listed in [`docs/audit-exceptions.txt`](docs/audit-exceptions.txt), and the
axiom audit fails on any file that surfaces an off-allowlist axiom without
being on that list. Long-form invariant,
roadmap, and build notes live in
[`docs/READING-GUIDE.md`](docs/READING-GUIDE.md#long-form-corpus-notes-off-the-readme-first-screen).

> **Licence.** [BSD-3-Clause](LICENSE), matching NetTopologySuite. The corpus is not archived for citation, so there is no DOI.

## 60 seconds

```sh
make help
```

`make help` works with no Rocq installed. Then [`docs/HELP.md`](docs/HELP.md).

## Contents

### `theories/` — Stdlib-only modules

Host CI target (`make host`). Foundational geometry on pairs of reals.

### `theories-flocq/` — Flocq binary64 modules

Plus the Stdlib-only Phase 3/4 modules built alongside them. Container only.

### `oracle/` — extracted reference driver

Consumed by [NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve), the out-of-tree incubator. The curve work itself has since moved in-tree — see [NetTopologySuite#857](https://github.com/NetTopologySuite/NetTopologySuite/pull/857) — so that repository is now a donor rather than the live path. Not a verified NTS runtime.

### `docs/` — actor cards, audits, registries

Start at [`docs/HELP.md`](docs/HELP.md).

### `dashboard/` — Observatory source

Generated status view; in-repo source of record only.

## Curve terminology

Where this corpus talks about curves it names the SQL/MM ISO/IEC 13249-3
types `CIRCULARSTRING` / `COMPOUNDCURVE` / `CURVEPOLYGON`. Linearisation
is the named `chord_approx` — `Linearise` here, `Linearize()` /
`ILinearizable` on the NTS side. NTS `Flatten()` to chords is lossy and
is not the curve.

## Reproduction

```sh
make help
make host
```

`make host` builds the 93 modules in `_CoqProject`, the foundational
Stdlib-only layer. The full corpus is 653 registered modules —
562 registered under `theories/` and 91 registered under
`theories-flocq/` — and is the pinned container.
Toolchain: **Rocq 9.2.0 + Flocq 4.2.2**. Those counts, the two
audit-exception counts above, and the `Defined.` count are checked against
the build inputs by
[`scripts/check_readme_counts.py`](scripts/check_readme_counts.py); the
claims around them by
[`scripts/check_readme_claims.py`](scripts/check_readme_claims.py). Both run
in `make ci-guards`.

## What this is not

- **Not** a verified implementation of NTS. The C# is not extracted from Rocq. Proofs are over an abstract model; they apply only when the implementation encodes the same mathematics.
- **Not** a substitute for unit tests. Tests still cover rounding, exceptions, performance, and the rest of the runtime.
- **Not** complete. Coverage is the foundational layer plus early-to-mid chokepoint phases; gaps are named in the Reading Guide, not silent.

**On the result named Shewchuk-13.** It states a corpus postcondition — a half-ulp bound written `strict_succ_b64`. It is *not* a disproof of Shewchuk 1997 and should not be cited as one; see [Proofs #482](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/482).

## Doors

- [`docs/HELP.md`](docs/HELP.md) — pick your path
- [`docs/READING-GUIDE.md`](docs/READING-GUIDE.md) — full map + long-form status
- [`GETTING-STARTED.md`](GETTING-STARTED.md) — 60-second on-ramp
- [`CONTRIBUTING.md`](CONTRIBUTING.md) — how to add theorems

## Roles

Joost is BDFL on corpus honesty and pruning, not product owner. Jeroen is PO.
