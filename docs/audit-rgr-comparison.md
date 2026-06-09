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
- **RED.** `Linearise.regime3_counterexample` — a predicate linearization
  cannot preserve (honest negative).
- **OPEN.**
  - **Arc-line Scope B/C** — round-chain identity + forward-error bound for
    the arc-line intersection coordinate (the parameter is generally
    non-dyadic, so Scope A's on-the-nose identity stops at the prefix).
    Bounded; mirrors the Phase 1 Scope C work.
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
| **B/C-arc** | arc-line Scope B/C (round-chain + fwd-error) | Phase 4 | medium–high — gives arc-line callers a usable forward-error contract | **low–medium** — direct mirror of Phase 1 Scope C; primitive already half-built (Scope A Qed) | medium, bounded |
| **H2** | `extract_rings_valid` (DCEL ring validity) | Phase 3 | **high** — discharges 1 of the 3 named hypotheses of the live conditional overlay headline; pure structure, no JCT | medium — DCEL refactor + per-condition proofs; no external dependency | high (5–7 sessions) |
| **SD** | re-scoped fast-expansion-sum nonoverlap | Phase 0 | **low** — optimization only; full-plane soundness already shipped via exact int-det | high — re-aim O1–O8 against a weakened predicate; the half-ulp dominance args must be re-derived | high |
| **H1** | polygonal JCT (`parity_characterises_interior_cont`) | Phase 3 | high — the headline-completing piece | **high** — no stub, no reachable library; multi-month from scratch | very high, blocked on ecosystem |
| **arc-H** | arc Hobby / arc snap-rounding analog | Phase 4 | high (if it exists) — would open exact-arc noding | **very high** — no published analog; may have no true statement | unbounded |

---

## 3. Decision (sequencing, not correctness)

1. **Invest next in the bounded in-regime closures: C1 (Phase 2) and arc-line
   Scope B/C (Phase 4).** Both are the same low-risk move the corpus has
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
   - **H1** is blocked on an external JCT formalization the network policy
     can't reach; it stays a named hypothesis of the conditional headline (no
     stub, no Admitted), to be re-opened **if** a library lands (~1 week then).
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
remaining gap to the per-quotient `round`** — round-to-nearest's lack of an
outward guarantee is now the *only* thing separating compute from spec on the
grid. The residual core (cross-multiply through the exact integer denominators →
sign-of-integer-determinant) is documented at the foot of the file as the next
multi-session step. Verified: full corpus build clean, `check_admitted` (still
7, none new), `check_readme_axioms`, and the per-theorem axiom audit all pass.
