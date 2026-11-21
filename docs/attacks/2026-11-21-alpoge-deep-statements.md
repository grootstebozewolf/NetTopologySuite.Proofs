<!-- doc-kind: finding
date: 2026-11-21
Provenance: 87e1dc5
Theorems: `AlpogeDeepStatements.v : TopG`, `AlpogeDeepStatements.v : HostExW`, `AlpogeDeepStatements.v : poleData_statement`, `AlpogeDeepStatements.v : landau_pole_asym_statement`, `AlpogeSkeleton.v : stated_four_are_unrefined_items`
-->
# Alpöge main line: TopG, HostExW, poleData and landau_pole_asym stated in Rocq (statements only)

Requested: refine `TopG`, `HostExW`, `poleData` and `landau_pole_asym` in
Rocq under the corpus's three-axiom standard, as **statements only, no QED**.
**Done.**

`docs/h1-vacuity/AlpogeDeepStatements.v` contains only `Definition … : Prop`
(and supporting vocabulary). It has no `Theorem`, `Lemma`, `Axiom`,
`Parameter` or `Admitted`, so nothing about these four items is asserted.
Every statement's `Print Assumptions` is within `docs/axiom-allowlist.txt`,
and `scripts/audit_axioms.sh` is OK. The four items stay **unrefined** in the
ledger: `AlpogeSkeleton.v : stated_four_are_unrefined_items` checks that each
is an unrefined entry.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source.

## What is stated

| Lean | Rocq statement(s) | refined into |
|---|---|---|
| `TopG` (ZeroFreeAllOfTopG) | `TopG` | `HostExW`, `FReq.cls` (`cls`), `FamCore.Windows` (`FWindows`), `HypV`, `FamilyClassConnected`; plus `TopG_at_main_statement`, the instance at `GChi ψ` that the main line uses |
| `HostExW` (ThinScalesIffHostBound l.120) | `HostExW`, `HostExW_main_statement` (`hS`, ∀ψ) | `Scale`, `Scales la` with `ScalesMem`, `HostReq`; the opaque `RankVal`, `HostGood`, `Host.CT2` |
| `poleData` (poleData l.248) | `poleData_statement` | `PoleData` (all seven fields: meas, growth, laplace, pos, diff, iso, pole), `gm`, `zeroSet`; and `poleData_char_statement` (l.137), with residue `m·(−1/(ρ(ρ−1)))` |
| `landau_pole_asym` (LandauPoleAsym) | `landau_pole_asym_statement` | `landau_pole_asym_deriv_statement`: the k-th derivative of `c/(s−ρ)` is `c(−1)^k k!/(z−ρ)^{k+1}` |

**The quantifier structure follows the Lean source.** For example,
`HostExW`:
- ∀ε ∈ (0, 1/52), ∃ `CT2 C8 C5 c6 Cb x0`, with `1 ≤ C8` and `C5, c6, Cb > 0`;
- ∃ `S : Scales la`, ∀ scales `s` with `s.eps = ε`, `x0 ≤ s.x` and
  `S.Mem s`;
- ∃ `R`, `H`, `q0` with `RankVal`, `CT2` matching, `HostGood`, and `P`.

## Representation (statement level)

- **ℂ** is `R × R` (`Cc`), with `|z| = sqrt(re² + im²)`.
- **Analytic notions are defined from Stdlib:**
  - `EvPunct` is "eventually in a punctured neighbourhood";
  - `CDerivWithin` and `CDifferentiableOn` are ε-δ complex derivatives;
  - `CAnalyticAt` is a power series converging on a disc (`Un_cv` on its
    components);
  - `IterDerivs` stands for Mathlib's `iteratedDeriv` on an open set, where
    it is unique.
- **Powers** `x^a` are `AlpogeRealsQED2.v`'s allowlist-clean `rpc`.
- **Deep carriers are section variables**, as opaque as they are in the
  statements: `Ranks`, `Host`, `FamP`'s fields, `ChainTied`, `VVle`,
  `EAtH`, the L-function zero predicates.
- **Two substitutions, both forced by Stdlib:**
  1. **Integral.** Lean's Bochner integral in `PoleData.laplace` becomes the
     limit `T → ∞` of Riemann integrals over `[0,T]`, valued as limits of
     uniform Riemann sums of a Riemann-integrable function.
  2. **Measurability.** Mathlib's `Measurable g` becomes local Riemann
     integrability.
  For the functions in question (exponentially bounded, locally
  Riemann-integrable), these agree with the Lean notions. That agreement is
  a reading, not a proof.

## Finding: Stdlib's `RiemannInt` value carries `classic`

The first draft defined the Laplace integral with Stdlib's `RiemannInt` and
failed the audit. `Print Assumptions RiemannInt` shows
`Classical_Prop.classic`, while `Riemann_integrable`, `cos`, `sin` and
`sum_f_R0` are clean.

This joins the earlier findings for `ln` / `Rpower` / `exp_increasing`. For
corpus modules: **values of Stdlib integrals and logarithms are outside the
allowlist; integrability, the series-defined functions, and IVT are inside.**

## OUTCOME

**STATED (4/4), no proofs, as requested.** The statements are allowlist-clean
and audited. The ledger is unchanged: 39/53 refined, 24 proved over `R`, and
14 unrefined, 4 of which now have Rocq statements.

The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 4 / warn 1 (Stdlib RiemannInt value carries classic) / bug 0.**
