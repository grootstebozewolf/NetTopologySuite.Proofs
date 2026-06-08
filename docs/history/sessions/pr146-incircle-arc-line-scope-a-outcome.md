# PR #146 — `b64_inCircle` exactness + arc-line Scope A outcome

**Branch.** `claude/perron-incircle-b64-exact`

**PR.** [#146](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/pull/146)

**Outcome.** FULL SUCCESS — issue #64 ask #4b closed; ask #5a advanced to
Scope A. Both modules Qed-closed; no `Admitted` / `Axiom` / `Parameter`.

## Deliverables

| Module | Key theorems | Closes |
|---|---|---|
| `InCircle_b64_exact.v` | `b64_inCircle_exact_sound` (full-plane sign); `b64_inCircle_exact_for_small_int` + `b64_inCircle_B2R_sign_sound_small_int` (`\|coord\| ≤ 2¹¹`); Perron witness `perron_inCircle_sign_sound` | Issue #64 ask #4b; INCIRCLE_SIGN oracle bridge |
| `ArcLineIntersect_b64_exact.v` | `b64_arc_line_sP_R`, `b64_arc_line_sQ_R`, `b64_arc_line_dx_R`, `b64_arc_line_dy_R`; Perron hook `perron_arc_line_sP_exact` | Issue #64 ask #5a Scope A |

Registered in `_CoqProject.full`, `docs/verified-claims.md`,
`docs/issue-64-arc-primitives-triage.md`.

## Design notes

- **Degree-4 bound.** The in-circle lifted determinant is homogeneous degree 4,
  so the integer-exactness window is `|coord| ≤ 2¹¹` (chain peaks at
  `2⁵² < 2⁵³`), tighter than orient2d's `2²⁵`.
- **Perron witness.** Stage-10 thin sliver scaled to the `2¹¹` arc integer
  regime; chord endpoints `P = (1, 0)`, `Q = (2¹¹, 0)` carry opposite
  `inCircle_R_BP` signs — mirrors `KakeyaOrient2d_b64.v`.
- **Honest arc-line scoping.** Scope A proves only the Cramer prefix before
  division. The headline `B2R (b64_arc_line_intersect_point_x …) =
  arc_line_intersect_x_R …` does **not** hold on the nose (intersection
  parameter is generally non-dyadic). Scope B (round-chain identity) and
  Scope C (forward-error bound) are queued.

## Review follow-up (`573f29b`)

- Header: eight coordinates / `b64_min_exp8` (was stale "sixteen"/`16`).
- License + AI-disclosure headers added.
- `perron_inCircle_Zdet_P/Q` wired into det_pos/neg proofs.
- Duplicate `arc_chord_diff_bound_2p12` removed; reuses `arc_diff_bound_2p12`.

## What this gates

- **INCIRCLE_SIGN** and ARC_* sign-products now have a machine-checked
  soundness story (not just bit-exact extraction).
- **Arc-line coordinates** — Scope B/C is the natural next terminal.