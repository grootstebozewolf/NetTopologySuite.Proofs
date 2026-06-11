# Cross-audit RGR comparison: ranking the open targets by risk/cost

**Status.** Written 2026-06-09. The six `audit-*` documents each scope one
chokepoint (Phase 0 Shewchuk stages, Phase 2 snap-rounding, Phase 3 overlay
×2, Phase 4 curves ×2). Individually they answer *"what's reusable / what's
the theorem / how is it milestoned"*. None of them answers the question that
actually drives the single-maintainer queue: **given everything still open
across all phases, which target is the best next proof investment?**

This document is that cross-cut. It applies the
[`snap-rounding-rgr-pivot.md`](snap-rounding-rgr-pivot.md) lens — frame each
area as a Red–Green–Refactor cycle, then rank the *live* open targets by
risk/cost — to the union of the audit-* docs. Same shape as the pivot doc and
as [`soundness-strategy.md`](soundness-strategy.md)'s Path 1 / Path 2 split:
the choice is effort-vs-coverage, **not correctness**. Nothing here is
deleted, disproved, or admitted; it is a sequencing recommendation.

It is grounded in the *live* registries, not the audit docs' (often stale,
self-flagged) snapshots:

- `docs/admitted-deferred-proofs.txt` — **1 live entry**: `extract_rings_valid`.
- `docs/admitted-counterexamples.txt` — the false-as-stated theorems
  (Shewchuk Thm 13 nonoverlap, `hobby_lemma_4_3_no_proper`, the grow-expansion
  family). These are **closed questions**, not open targets.
- `docs/verified-claims.md` — the Qed-closed GREEN per phase.

---

## 1. Where each audit area's RGR cycle stands

For each area: what is **RED** (machine-checked negative / the gap proven
real), what is **GREEN** (the Qed-closed primitive that ships), and what is
genuinely **OPEN** (a true theorem with no proof yet — the only thing worth
ranking).

### Phase 0 — Shewchuk stages B/C/D ([`audit-shewchuk-stages.md`](audit-shewchuk-stages.md))

- **GREEN.** Full-plane `orient2d` soundness ships via the *exact
  integer-determinant* route (`b64_orient2d_exact`, 3 axioms) — see
  [`phase0-completion.md`](phase0-completion.md). Stages B/C/D landed as a
  sound error-free transform under `expansion_safe`
  (`B64_Expansion.v`, `sign_of_expansion_correct`, Dekker TwoProduct).
- **RED.** Two machine-checked negatives close the headline ambitions:
  `fast_expansion_sum_nonoverlap_shewchuk` is **FALSE as stated** (half-ulp
  `strict_succ_b64` ≠ Shewchuk's bit-disjoint nonoverlap;
  `B64_Shewchuk_Thm13_counterexample.v`), and Stage D **does not recover**
  catastrophic underflow (`stage_d_does_not_recover_under_underflow`); the
  integer-mantissa decoder does.
- **OPEN.** Only a *re-scoped* fast-expansion-sum nonoverlap (weaken the
  predicate to bit-disjoint, re-aim O1–O8). **Value is now an optimization,
  not soundness** — the exact int-det route already gives the sound
  full-plane predicate the B/C/D chain was originally the path to.

### Phase 2 — snap-rounding ([`audit-phase2-snap-rounding.md`](audit-phase2-snap-rounding.md), [`snap-rounding-rgr-pivot.md`](snap-rounding-rgr-pivot.md))

- **GREEN.** Hot-pixel layer, `b64_snap_round_preserves_passes_through`,
  bit-level snap idempotence, the exact R-spec passes-through (sound +
  complete + symmetric), and `hobby_theorem_4_1_conditional`.
- **RED.** The *rounded compute filter* is unsound, incomplete, and
  order-dependent (the JTS#752/#1133 root) — three Qed witnesses. And
  `hobby_lemma_4_3_no_proper` is **FALSE as stated** (parallel segments
  collapse onto one grid line → manufactured proper intersection).
- **OPEN.** **C1 grid exactness** (`compute ≡ spec` on integer/half-integer
  coordinates). Strongly evidenced (0 divergence in 5M on-grid cases), not yet
  proven. This is the [`snap-rounding-rgr-pivot.md`](snap-rounding-rgr-pivot.md)
  recommended next target — it converts the RED's "unsound off-grid" into a
  constructive "**sound on the snap grid**", the regime a noder actually
  operates in. (C2 — rounded-filter completeness — is the blocked square the
  pivot doc already said STOP to; not re-litigated here.)

### Phase 3 — overlay ([`audit-phase3-overlay.md`](audit-phase3-overlay.md), [`audit-phase3-milestone5.md`](audit-phase3-milestone5.md))

- **GREEN.** Geometry/`boolean_op` semantics, the topology graph, label
  merging, `correct_labels_all_ops`, and the Qed-closed conditional headline
  `overlay_ng_correct_conditional` under three named hypotheses (H1 JCT, H2
  `extract_rings_valid`, H_bridge).
- **RED.** The JCT seam's first formulation `geometric_interior_stdlib` was
  machine-checked **vacuous** (`geometric_interior_stdlib_vacuous`); H1 was
  re-pointed onto the continuous `geometric_interior_cont`, and the remaining
  JCT content isolated as `parity_characterises_interior_cont`.
- **OPEN (two, very different sizes).**
  - **H2 — `extract_rings_valid`** (DCEL ring assembly produces valid
    polygons). The **single live deferred-proof registry entry**. Pure
    structural reasoning, no JCT, no point-set semantics. 5–7 sessions
    (DCEL path).
  - **H1 — polygonal JCT** (`parity_characterises_interior_cont`).
    Thesis-scale; **no Coq stub exists** because stating it faithfully needs a
    topology toolkit the corpus lacks, and the ecosystem search
    ([`jct-scout-2026-05-29.md`](jct-scout-2026-05-29.md)) found **no usable
    JCT formalization** reachable under the network policy. 3–5 months from
    scratch; ~1 week if a library lands.

### Phase 4 — curves ([`audit-phase4-curves.md`](audit-phase4-curves.md), [`audit-phase4-chord-overfitting.md`](audit-phase4-chord-overfitting.md))

- **GREEN.** Both lines landed and coexist. Option B (chord approx):
  `Linearise.v`, `ArcChordApprox.v`, `CurveLinearise.v`, the conditional
  `arc_overlay_correct_chord_approx`. Option A (exact arc, issue #64): atan2 /
  angle-between / `r·θ` arc length, and the binary64 in-circle layer
  `b64_inCircle_exact_sound` (**full-plane sign, 3 axioms**) + arc-line Scope A.
  **Arc-line Scope B and C are now also GREEN** (closed 2026-06-10, §6): the
  bit-exact denominator (B.1), the full round-chain identity (B.2), and the
  **absolute `bpow 13` forward-error bound** of the intersection coordinate vs
  the exact real value (C, `b64_arc_line_point_{x,y}_forward_error`).
- **RED.** `Linearise.regime3_counterexample` — a predicate linearization
  cannot preserve (honest negative).
- **OPEN.**
  - **Arc Hobby / arc snap-rounding analog** — **research gap, no published
    analog of Hobby's theorem for arcs.** Same epistemic shape as the (now
    refuted) `hobby_lemma_4_3_no_proper`: thesis-scale, possibly multi-month,
    no guarantee of a true statement at the end.

---

## 2. Risk/cost of the live open targets

Only **true, unproven** targets are ranked (the false-as-stated theorems are
closed questions in the counterexample registry; C2 was parked by the pivot
doc). Risk = tractability / chance the effort yields something shippable.

| # | target | area | value | risk (tractability) | cost |
|---|---|---|---|---|---|
| **C1** | grid exactness `compute ≡ spec` on-grid | Phase 2 | **high** — recovers in-regime **soundness** of the noder filter (the headline the RED denies off-grid) | **low–medium** — same integer/dyadic exactness style as `Orient_b64_exact` (Path 2) & snap idempotence; 0/5M divergence | medium, bounded |
| ~~**B/C-arc**~~ | ~~arc-line Scope B/C (round-chain + fwd-error)~~ — **LANDED 2026-06-10 (§6)** | Phase 4 | medium–high — arc-line callers now have an absolute `bpow 13` forward-error contract | — | **done** |
| **H2** | `extract_rings_valid` (DCEL ring validity) | Phase 3 | **high** — discharges 1 of the 3 named hypotheses of the live conditional overlay headline; pure structure, no JCT | medium — DCEL refactor + per-condition proofs; no external dependency | high (5–7 sessions) |
| **SD** | re-scoped fast-expansion-sum nonoverlap | Phase 0 | **low** — optimization only; full-plane soundness already shipped via exact int-det | high — re-aim O1–O8 against a weakened predicate; the half-ulp dominance args must be re-derived | high |
| **H1** | polygonal JCT (`parity_characterises_interior_cont`) | Phase 3 | high — the headline-completing piece | ~~**high** — no stub, no reachable library; multi-month from scratch~~ **re-graded medium 2026-06-10 (see Postscript)** — trapped half Qed unconditionally; one named residual (`even_parity_escapes`) | ~~very high, blocked on ecosystem~~ **bounded, in-corpus** |
| **arc-H** | arc Hobby / arc snap-rounding analog | Phase 4 | high (if it exists) — would open exact-arc noding | **very high** — no published analog; may have no true statement | unbounded |

---

## 3. Decision (sequencing, not correctness)

1. **Invest next in the bounded in-regime closures: C1 (Phase 2) and arc-line
   Scope B/C (Phase 4).** *(Both now LANDED — see §5 and §6.)* Both are the same low-risk move the corpus has
   shipped repeatedly — exactness/forward-error in a regime — and both
   *deliver a soundness/contract headline* their callers can actually use. C1
   has the edge because it converts a documented unsoundness (the JTS#752/#1133
   root) into a constructive in-regime guarantee; it is the recommendation
   [`snap-rounding-rgr-pivot.md`](snap-rounding-rgr-pivot.md) already named.

2. **Then take `extract_rings_valid` (Phase 3 H2)** as the highest-value
   *structural* target. It is the **only live deferred-proof entry**, it needs
   no JCT and no external library, and closing it discharges one of the three
   hypotheses gating the conditional overlay headline — moving the Phase 3
   story strictly forward within the corpus. Higher cost than C1, but the risk
   is execution (DCEL bookkeeping), not tractability.

3. **STOP chasing the three high-risk squares: polygonal JCT (H1), the arc
   Hobby analog, and the Shewchuk re-scope (SD).** These are this comparison's
   analogue of the pivot doc's C2 — demote them to *useful, honestly-recorded
   open obligations*, not critical path:
   - **H1** ~~is blocked on an external JCT formalization the network policy
     can't reach; it stays a named hypothesis of the conditional headline (no
     stub, no Admitted), to be re-opened **if** a library lands (~1 week then).~~
     **Superseded 2026-06-10 — see the Postscript:** the trapped half is now
     Qed unconditionally for every closed ring (`JCTTrappedHalf.odd_parity_trapped`)
     and the seam is reduced to the single residual `even_parity_escapes`;
     H1's risk shifted from *existence* to *execution*, which by this doc's
     own criterion promotes it off the stop-chasing list.
   - **arc-H** has no published true statement — same risk profile as the
     refuted `hobby_lemma_4_3_no_proper`. Defer until a downstream consumer
     forces exact-arc noding (the Phase 4 tripwire, ~2031).
   - **SD** is now an *optimization*, not soundness — full-plane `orient2d`
     already ships via exact int-det. Re-scoping nonoverlap is real work for
     no soundness gain; leave it as the documented bit-disjoint follow-up.

### Why this is the risk/cost-optimal ordering

The corpus has one repeatable, low-risk, high-yield move — **bit-exactness or
forward-error in a regime** (`Orient_b64_exact` Path 2, snap idempotence,
in-circle integer regime, arc-line Scope A). C1 and arc-line Scope B/C are
exactly that move, and each ends on a usable headline. `extract_rings_valid`
is a different but still *bounded* bet: structural, no external dependency,
and it visibly advances the flagship Phase 3 theorem. The three deferred
squares all share the property that sank C2 and the Shewchuk Thm-13 headline —
the effort can yield nothing shippable (no reachable library, no published
theorem, or no soundness gain). Same evidence-vs-execution asymmetry the pivot
doc used: **prefer the targets whose risk is execution over the targets whose
risk is existence.**

---

## 4. Future paths left open

- **C1 → in-regime soundness corollary** (compose with
  `b64_passes_through_sound`), exactly as
  [`snap-rounding-rgr-pivot.md`](snap-rounding-rgr-pivot.md) §"Future paths"
  describes.
- **H1 (polygonal JCT)** stays a named, non-vacuous hypothesis of
  `overlay_ng_correct_conditional`; re-open on a usable library landing
  (`jct-scout-2026-05-29.md` is the standing search).
- **H2 → `valid_geometry_extract` unconditional** and a stronger overlay
  headline once the DCEL ring validity closes.
- **arc-H / SD** remain available for anyone wanting the deeper coverage; the
  precise blockers and evidence are recorded in their source audits and the
  counterexample registry.

The corpus invariant — no `Admitted`, no `Axiom`, no `Parameter` beyond the
recorded allowlists — holds throughout and is preserved by this sequencing:
it adds no obligations, it only orders the ones already on the books.

---

## 5. Execution — RGR slice landed on the #1 target (2026-06-09)

Acting on §3's ranking, the next RGR slice was driven on the top target, **C1
grid-exactness** (`theories-flocq/PassesThrough_b64_grid_exact.v`). The file
already carried Slices 1–5 (the on-grid reduction to a single touch, the
integer-grid↔fixed-point bridge, the slab-guard bridge, operand exactness, and
the max/min composition — all `Qed`). This session added **Slice 6, the
division bridge**, `Qed`-closed at the allowlisted 4-axiom footprint (no new
`Admitted`/`Axiom`):

- `b64_div_round_half_over_int` — a half-integer numerator over a nonzero
  integer denominator divides bit-correctly to the rounded exact quotient;
  discharges the last `b64_div_correct` no-overflow obligation on the grid
  (`|num/den| ≤ |num| ≤ 2²⁸ < 2^emax`).
- `b64_lb_tlo_eq_rounded_quotients_grid` (+ `_thi_`) — each per-axis compute
  t-bound equals the exact-spec t-bound with each quotient *individually
  rounded*.

This is the RED→GREEN→refactor pattern this corpus uses: the RED (the rounded
filter is unsound / incomplete / order-asymmetric off-grid) was already `Qed`;
Slice 6 advances the GREEN (on-grid agreement) by **localising the entire
remaining gap to the per-quotient `round`**.

**Continued (2026-06-09, slices 7–9).** Driving the cycle further closed one of
C1's two directions outright:

- Slices 7–8 (`b64_lb_tlo_eq_round_exact_grid`, `b64_tmin_eq_round_exact_grid`,
  + `_thi`/`_tmax`): rounding is monotone, so it commutes past `Rmin`/`Rmax` and
  the outer clip — every compute t-bound, and the whole clipped `tmin`/`tmax`,
  collapses to a *single* `b64_round` of the exact spec value.
- **Slice 9 (`b64_passes_through_complete_on_grid`, `Qed`):** **on-grid
  completeness** — `spec ⇒ compute` on the integer grid, i.e. the rounded filter
  **never drops a pass** (the noder-safe direction). Free from monotonicity once
  Slice 8 expresses the compute bounds as `round` of the exact ones.

That leaves only the on-grid **soundness** direction (`compute ⇒ spec`) open,
now isolated to the single real comparison `round tmin_e ≤ round tmax_e ⟹
tmin_e ≤ tmax_e` (the cross-multiply → integer-determinant-gap argument), tracked
at the foot of the file. Verified each step: full corpus build clean,
`check_admitted` (still 7, none new), `check_readme_axioms`, and the per-theorem
axiom audit all pass; the completeness headline closes at the allowlisted
4-axiom footprint.

**Continued (slice 10 — conditional headline).** `b64_passes_through_grid_exact_cond`
(`Qed`) certifies the *full* on-grid `compute = spec` equivalence modulo a single
named real hypothesis — the corpus's `hobby_theorem_4_1_conditional` pattern, no
`Admitted`/`Axiom` (the gap is a plain `Prop` hypothesis). Its `=true` half is
free (slice 9 completeness); only the `=false` (soundness) half is open. The
file's obligation note now carries the integer-determinant gap analysis with a
concrete finding: the gap argument closes **unconditionally for `|n| ≤ 2²³`**
(then `|d_a·d_b| ≤ 2⁴⁸`, gap `> ulp`), but is **borderline at the full
`coord_int_safe` width `2²⁵`** (gap can fall to `~2⁻⁵⁴ < ulp`), so a full-width
unconditional close needs the exact integer-determinant comparison, not a
forward-error bound.

**Continued (slice 11 — rounding-reflection kernel).** `round_reflects_le_of_sep`
+ `round_diff_le_of_round_le` (`Qed`): round-to-nearest moves each value `≤ ½ ulp`,
so the rounded `≤` reflects the exact `≤` once the values are ordered or
separated beyond the half-ulp band. This **removes the rounding from slice 10's
hypothesis**, replacing it with the pure-reals `clip_separated` — on-grid
soundness now hinges only on the exact clip bounds being ulp-separated, which is
exactly the integer-determinant gap (no `Rle_bool`-of-rounds left).

**Continued (slice 12 — determinant-gap kernel).** `rational_gap` (`Qed`): two
distinct rationals `na/da`, `nb/db` differ by `≥ 1/(|da||db|)` (the difference is
a nonzero integer over `da·db`); `grid_quotient_ratio` exposes each grid t-bound
as `IZR(m−2n₀)/IZR(2(n₁−n₀))`, so the binding `tmin_e − tmax_e` gap is
`≥ 1/(|2(x₁−x₀)|·|2(y₁−y₀)|)`. This is the **gap (lower-bound) half** of
`clip_separated`, proven.

**Continued (slice 13 — ulp upper bound).** `b64_ulp_round_le_bpow` (`Qed`):
`round x` stays in the binade of `x`, so `|x| ≤ 2ᵉ ⇒ ulp(round x) ≤ 2^(e+1−prec)`
(via `b64_round_abs_le_bpow` + Flocq `ulp_le`/`ulp_bpow`); the `[0,1]` instance
`b64_ulp_round_le_unit` gives `ulp(round x) ≤ 2⁻⁵²`. The **upper-bound half** of
`clip_separated`.

**Continued (slice 14 — the bricks combine).** `grid_ratio_gap_exceeds_ulp_band`
(`Qed`): for two distinct ratios `u=na/da`, `v=nb/db` in `[-1,1]` with
`|da|,|db| ≤ 2²⁴`, `½ulp(round u)+½ulp(round v) < |u−v|` — band `≤ 2⁻⁵²` (slice
13), gap `≥ 2⁻⁴⁸` (slice 12), `2⁻⁵² < 2⁻⁴⁸`. This is **exactly `clip_separated`'s
right disjunct** for the binding `(tmin_e,tmax_e)` pair — the determinant-beats-
rounding inequality, the quantitative heart of unconditional on-grid soundness
for `|n| ≤ 2²³`. The only remaining step is purely structural: exhibit `tmin_e`,
`tmax_e` as such bounded ratios (each `Rmax`/`Rmin` selects one of
`{0,1,tlo_x,tlo_y,thi_x,thi_y}`) and apply slice 14 — no analytic content left.

**Closed (slices 15–18 — C1 unconditional on the tight grid).** Slice 15
(relative ulp bound) removed the `[-1,1]` cap; slice 16 added the value-0 edge;
slice 17 (`gridbound` algebra) packaged "gap beats band" as
`gap_beats_band_of_gridbound`; slice 18 showed each exact clip bound is
`gridbound` (`gridbound_tlo`/`thi` via `gridbound_half_quotient`) and hence
discharged `clip_separated` outright. **Result: `b64_passes_through_grid_exact`
(`Qed`) — `compute = spec` UNCONDITIONALLY for integer-grid points with
`|n| ≤ 2²²`, no named hypotheses** (soundness `b64_passes_through_sound_on_grid`
+ slice-9 completeness). C1 is closed in the regime a snap-rounding noder runs
in; the only open items are the width extension to `2²⁵` (needs the exact
integer-determinant comparison) and the general-binary64 C2.

---

## 6. Execution — RGR slices landed on the #1 co-target: arc-line Scope B/C (2026-06-10)

§3's ranking named **two** co-#1 bounded in-regime closures: C1 (closed in §5)
and **arc-line Scope B/C** (`theories-flocq/ArcLineIntersect_b64_exact.v`). This
section logs the latter, now closed end-to-end. Starting point was Scope A
(`b64_arc_line_{sP_R,sQ_R,dx_R,dy_R}`, `Qed`): the Cramer prefix before the
dividing step is bit-exact. Scope A's *on-the-nose* coordinate identity does
**not** extend past the division (the intersection parameter is generally
non-dyadic), so the honest ladder is round-chain identity (B) then forward-error
bound (C). All slices below are `Qed` at the allowlisted 4-axiom footprint
(`Classical_Prop.classic` via the b64-arithmetic lineage, already exempted in
`docs/audit-exceptions.txt`); no new `Admitted`/`Axiom`/`Parameter`.

- **Scope B.1 — bit-exact denominator (#158).** `b64_arc_line_den_exact`
  (+ `_den_nonzero`): the divisor `den = sP − sQ` is computed *bit-exactly*
  (`= inCircle_R_BP P − inCircle_R_BP Q`, finite) — both inCircle values are
  integers `≤ 2⁵²`, so their difference `≤ 2⁵³ = 2^prec` rounds to itself — and
  is nonzero under the safety predicate. Exposed the prerequisite
  `b64_inCircle_finite_for_small_int` (a projection of the refactored
  `b64_inCircle_exact_and_finite_for_small_int`).

- **Scope B.2 — full round-chain identity (#159).**
  `b64_arc_line_intersect_point_{x,y}_round_chain`: the *entire* coordinate
  computation equals its IEEE-754 round-chain of the exact-real operands,
  `B2R(point_x) = round(B2R(bx P) + round(round(sP/(sP−sQ)) · (B2R(bx Q) −
  B2R(bx P))))` (and `y`). Each `div → mult → plus` step discharged via
  `b64_{div,mult,plus}_correct` with magnitude gates
  (`|sP| ≤ 2⁵²`, `|den| ≥ 1`, `|d| ≤ 2¹²`, `t·d ≤ 2⁶⁴`, sum `≤ 2⁶⁵ < 2^emax`).
  The exact statement of *what the float intersection computes*.

- **Scope C layer 1 — division forward error (#160).**
  `b64_arc_line_t_forward_error`: the parameter `t` drifts from the exact-real
  ratio `sP_R/(sP_R−sQ_R)` by `≤ ½` (one division half-ulp). The bit-exact
  denominator (B.1) means **no denominator-carryover** — the structural payoff
  that keeps the whole cascade absolute, unlike the line-line layer 1 whose
  denominator rounds.

- **Scope C layer 2 — multiply forward error (#161).**
  `b64_arc_line_mult_{x,y}_forward_error`: the `t·d` product deviates from
  `ratio·d_R` by a clean `bpow 12` (multiply half-ulp `bpow 11` + layer-1 carry
  `bpow 11`). **No `1/|den|` term** — the line-line analog instead carries a
  `bpow 80/|den|` condition-number tail.

- **Scope C capstone — layers 3–4 / headline.**
  `b64_arc_line_point_{x,y}_forward_error`: the float intersection coordinate is
  within **`bpow 13`** of the exact real value,
  `|B2R(b64_arc_line_intersect_point_{x,y} …) − arc_line_intersect_{x,y}_R …| ≤
  bpow 13`. Layer 3 (final `bx P + ·` add) contributes a half-ulp at magnitude
  `≤ 2⁶⁵` (`≤ bpow 12`); plus the layer-2 carry (`≤ bpow 12`); total `bpow 13`.

This is the same RED→GREEN→refactor / "exactness-or-forward-error-in-a-regime"
move §3 identified as the corpus's repeatable low-risk play. The arc-line
result lands on the headline §2 predicted — an **absolute** forward-error
contract with **no `1/|den|` condition-number blow-up**, because every layer
inherits the bit-exact denominator. Each slice verified: file compiles clean,
`check_admitted` (still 7, none new), `check_readme_axioms`, `validate-claims`,
and the per-theorem axiom audit all pass.

With both co-#1 targets (C1, arc-line Scope B/C) now closed, the
risk/cost-ordered queue advances to **§3 item 2: `extract_rings_valid`
(Phase 3 H2)** — the highest-value *structural* target and the single live
deferred-proof registry entry.

---

## Postscript (2026-06-10, evening): H1 re-graded

The H1 row above ("polygonal JCT, **high** risk — no stub, no reachable
library; multi-month from scratch; very high cost, blocked on ecosystem")
is superseded. In one sustained push
(`docs/jct-on-edge-counterexample.md`, Follow-ups 1–9, and
`theories/JCT{ParityTransport,HalfOpenParity,GenericStability,LevelJump,
TrappedHalf,SeamAssembly}.v):

- the seam was **corrected** (the strict form is refutable at on-edge
  points; the off-ring form is the honest target);
- the corrected seam was discharged **totally** for three families
  (rectangle, arbitrary CCW triangle, right triangle) with a generic
  convex assembly awaiting n-gon parity obligations;
- the **trapped half** of the polygonal JCT — its load-bearing direction —
  is now **Qed, unconditionally, for every closed ring**
  (`JCTTrappedHalf.odd_parity_trapped`), via a decidable-invariant
  transport engine, the half-open parity, and a telescoping east-level-flag
  argument that replaced the feared vertex-pairing case explosion;
- the full seam is reduced to **one named per-point residual**,
  `even_parity_escapes` (`JCTSeamAssembly.v`) — the escape construction
  for even-parity points of SIMPLE rings, the only place simplicity is
  needed.

New grade: **medium** — one residual, in-corpus, with a concrete proof
obligation (boundary-following or staircase escape for simple polygons);
no external library required after all. The "blocked on ecosystem" verdict
is retired: the ecosystem gap was routed around entirely within the
corpus's three-axiom budget.

---

## 7. Execution — first #65 curve-buffer brick on top of the closed #64 contract: arc offset (2026-06-11)

§6 closed arc-line Scope B/C, and the issue-#65 verdict flipped from
"blocked on #64" to "unblocked — the open work shifts to the curve-buffer
proofs themselves: arc offset (parallel curve at distance d), join
soundness on curved inputs, topology preservation for `CurvePolygon`
output". This section logs the first of those bricks:
**`theories/ArcOffset.v`** — the Stage 2a-CURVE seam of the buffer/noder
pipeline (`buffer-noder-pipeline.md` §2.2), the curved analogue of
`BufferOffset.v`. All headlines `Qed` at the **three-axiom** footprint
(including the derivative bridges — `Rtrigo_reg`'s
`derivable_pt_lim_{sin,cos}` turn out classic-free, unlike `atan` /
`sin_lt_x`); no new `Admitted`/`Axiom`/`Parameter`.

- **AT DISTANCE d, globally (`arc_offset_dist_exact`).** The concentric
  radius-`r+d` curve is *exactly* at distance `|d|` from the source
  circle: every circle point is `≥ |d|` away (reverse triangle
  inequality through the center, via `Linearise.dist_triangle`) and the
  radial correspondent attains it (`arc_offset_radial_dist`). Valid for
  `0 ≤ r`, `−r ≤ d` — i.e. up to and including the singularity. This is
  the defining parallel-curve property, the curved
  `offset_point_dist`/`offset_perp_dist_to_line`.

- **PARALLEL / no kink (`arc_offset_no_kink`).** The offset tangent is a
  *positive* scalar multiple (`(r+d)/r`) of the source tangent before
  the singularity — offsetting cannot rotate or reverse the direction of
  travel (curved `offset_seg_dir`, the JTS#739/#180 kink class). The
  tangents are genuine `derivable_pt_lim` derivatives of the
  parametrisation (`circle_point_{x,y}_deriv`), not decreed.

- **Singularity, quantitatively (`arc_offset_tangent_dot` = `r(r+d)`).**
  Positive before `d = −r`, zero at it, negative past it
  (`arc_offset_tangent_reverses_past_singularity`) — the cusp +
  direction-reversal behind inverted negative arc buffers.

- **Honest negative (`inner_offset_past_center_not_at_distance`).**
  Concrete `Qed` witness (`r = 1`, `d = −3`): past the singularity the
  parallel-curve property itself *fails* (the "offset" point is at
  distance `1 < |d| = 3` from the circle). Emitting
  `circle_point C (r+d)` there is unsound, not merely inverted — the
  guard a curve-aware buffer must enforce.

- **Length bridge (`arc_offset_length`).** Over the same sweep,
  `arc_length (r+d) θ = arc_length r θ + d·θ` (M-LEN seam to
  `ArcLength.arc_length`).

Still open on the #65 curve lane (in pipeline order): emitted curve-aware
offset *edge lists* + join/cap edges on curved inputs, the
SQL/MM-three-point bridge (`CurveGeometry.arc_center`/`arc_radius` to the
center/angle form used here), and `CurvePolygon` topology preservation.
The next bounded slice of the same shape is the three-point bridge (pure
algebra, no new analysis); the assembly-level targets ride on the same
Option-B machinery as the linear pipeline.

**Rung 2 (2026-06-11, same day): the three-point bridge landed.**
`theories/ArcOffsetThreePoint.v`, all `Qed`, three-axiom. The radial
offset as a homothety about the center (pure rational arithmetic, no
trig) carries the parallel-curve property into coordinate form
(`radial_offset_dist_exact`); the **circumcenter-uniqueness** lemma that
`CurveGeometry.v`'s §2 comment had deferred is closed
(`equidistant_point_is_arc_center` — perpendicular-bisector system +
Cramer against the explicit `arc_center` formula, the predicted fiddly
square that in fact fell to `field_simplify_eq` + `nra`); and the
closure headline `arc_offset_preserves_arc` proves the radial offset of
a valid three-point `CircularArc` is again a valid three-point
`CircularArc` with the **same `arc_center` and `arc_radius = r + d`** —
"buffer/offset preserving arcs" (#65 BUF-*/OFF) at the representation
level, extractable as-is. Remaining on the lane: emitted offset edge
lists, joins/caps on curved inputs, `CurvePolygon` topology preservation.

**Rung 3 (2026-06-11): segment-wise COMPOUNDCURVE offset.**
`theories/CurveRingOffset.v`, all `Qed`, three-axiom. `curve_ring_offset`
maps a `CurveRing` segment-wise (chords via `BufferOffset.offset_point`,
arcs via rung 2's `arc_offset_arc`); per-arc validity and segment count
survive under the per-arc safety bound `−r < d`
(`curve_ring_offset_arcs_valid`). The join story is now split honestly:
**G1 joins with consistent unit normals offset continuously**
(`arc_join_offset_continuous` — smooth compound curves need no join
edges), while **tangent-line continuity alone provably does not
suffice** (`tangent_continuity_insufficient_for_offset` — a concrete
S-curve/inflection witness with anti-parallel normals where the `d = 1`
offset tears the shared point to `(2,0)` vs `(0,0)`; the arc-side
JTS#1147 / OffsetCurve artifact class, and the reason stage-2b join
edges remain on the ladder). Remaining: join/cap edge emission for the
non-G1 case, adjacency/closedness lifting for all-G1 rings, and
`CurvePolygon` topology preservation.

**Rung 4 (2026-06-11): the lift to whole rings — smooth rings stay valid.**
Same file (`CurveRingOffset.v` §§5–7), all `Qed`, three-axiom. A uniform
offset normal field across both segment kinds (`segment_norm_{end,start}`:
chords carry `unit_perp`, arcs the outward unit radial) factors both
offset formulas through `P + d·n̂`, so one join lemma
(`segment_join_offset_continuous`) covers chord-chord, chord-arc, and
arc-arc joins (coherent with rung 3's arc-arc condition via
`join_normals_consistent_norm_iff`). List induction lifts it:
`curve_ring_offset_adjacent` and `curve_ring_offset_closed` preserve
adjacency/closedness for rings whose consecutive + closing joins all
have consistent normals, and the capstone `curve_ring_offset_valid`
closes the ring-level structural story — a smooth compound ring offset
within the per-arc safety bound is again a `valid_curve_ring`, ready for
SQL/MM `CurvePolygon` boundary emission. Remaining on the #65 ladder:
join-edge emission for the non-G1 case (forced by rung 3's tear
witness), endcaps on curved inputs, and `CurvePolygon`-level topology
(hole/shell relations) under offset.
