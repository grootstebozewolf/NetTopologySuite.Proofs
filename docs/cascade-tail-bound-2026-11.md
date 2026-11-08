# Cascade tail bound and closed look-ahead, arbitrary length (paper proof)

Status: **mechanized in Rocq** (FLX model) — `docs/h1-vacuity/CascadeTailBound.v :
cascade_tail_bound`, `cascade_closed_lookahead` (Qed, no Admitted; axioms: Reals + `classic` +
functional extensionality, as the corpus). The keys (F1) and Lemma S are proved there from the
Priest chains, not assumed. Not covered: binary64 underflow and the link to
`b64_grow_expansion_aux`. Model checks of every step: `tests/CascadeInvariantProbe/lemmas.py`,
`lemmas_rand.py`. SUMMARY ok=1 warn=1 bug=0 (warn: FLX model, not binary64).

## Model and hypotheses

- Radix 2, precision p >= 2, round-to-nearest ties-to-even `RN`, **unbounded exponent range**
  (no underflow, no overflow). For binary64 this means all values involved stay normal and finite.
- `e`, `f` Priest chains (adjacent components: normalised p-bit significands, exponent gap >= p),
  all components **nonzero**.
- `g_0, ..., g_n`: the components of `e ++ f` sorted by `|.|` ascending (ties in any order).
- Cascade: `Q_0 = g_0`; `Q_j = RN(g_j + Q_{j-1})`; `h_j = g_j + Q_{j-1} - Q_j` (exact).
- `U_j = ulp(g_j) = 2^(mag(g_j) - p)`, where `2^(mag x - 1) <= |x| < 2^(mag x)`.
- Exact sums: `S_j = sum_{i<=j} g_i`, `H_j = sum_{1<=i<=j} h_i`, so `S_j = Q_j + H_j`.

Basic facts used:

- (F1) keys: `|g_j| < U_{j+2}`. This is `priest_keys_general` (Qed for binary64 in
  `B64_CarryCleanLadder.v`; the counting argument is format-generic).
- (F2) `|x| <= |y|` implies `ulp x <= ulp y`. In particular `U_j` is nondecreasing.
- (F3) RN is nondecreasing and odd, and fixes representables. So if `z` is representable and
  `x <= z`, then `RN x <= z`. Below the midpoint of consecutive representables `r1 < r2`, RN
  gives at most `r1`.
- (F4) A multiple of `2^s` with magnitude at most `2^(s+p)` is representable. In the binade
  `[2^(e-1), 2^e)` the representables are the multiples of `2^(e-p)`.
- (F5) Ties-to-even: `RN(2^e + 2^(e-p)) = 2^e`, because `2^e` has the even significand.

## Lemma S (exact partial sum)

`|S_{k-2}| < 2 U_k`.

Proof. By (F1) every `g_j` with `j <= k-2` has `|g_j| < U_{j+2} <= U_k`. Within one chain, the
consumed components are that chain's smallest ones. Write them `a_1, a_2, ...` (decreasing),
with `a_i = m_i 2^(k_i)`. Since `2^(k_1 + p - 1) <= |a_1| < U_k`, `2^(k_1)` divides `U_k`, so
`|a_1| <= U_k - 2^(k_1)`. Priest gives `|a_{i+1}| < 2^(k_{i+1} + p) <= 2^(k_i)`, and `a_{i+1}`
is a multiple of `2^(k_{i+1})`, so `|a_{i+1}| <= 2^(k_i) - 2^(k_{i+1})`. Telescoping gives a
chain sum of at most `U_k - 2^(k_last) < U_k`. Two chains give `< 2 U_k`. ∎

## Lemma U (ulp sum)

`sum_{j=1}^{k-2} U_j < 2 U_k / (2^p - 1)`.

Proof. By (F1), `|g_j| < U_{j+2}` and `U_{j+2}` is a power of two, so
`U_j <= 2^(-p) U_{j+2}`. Then `U_{k-2}, U_{k-3} <= 2^(-p) U_k`,
`U_{k-4}, U_{k-5} <= 2^(-2p) U_k`, and so on. The sum is below
`2 U_k sum_{i>=1} 2^(-ip) = 2 U_k / (2^p - 1)`, strictly because the sum is finite. ∎

## Theorem

For every `1 <= k <= n`:

- **T(k)**: `|Q_{k-1} - g_{k-1}| <= 2 U_k`;
- **LA(k)**: `|h_k| <= U_k`. In particular `|h_k| <= ulp(g_{k+1})`, the closed look-ahead.

Proof by strong induction on k. `T(1)` holds trivially: `Q_0 - g_0 = 0`.

### Step A: T(k) implies LA(k)

Let `g = g_k`, `u = U_k`, `m = mag g`, `a = g_{k-1}`, so `|a| <= |g| <= 2^m - u`.

- If `|a| >= 2^(m-1)`: `a` is a multiple of u, so `|a| <= 2^m - u`, and T(k) gives
  `|Q_{k-1}| <= 2^m + u`. No representable lies in `(2^m, 2^m + 2u)`, so `|Q_{k-1}| <= 2^m`.
- If `|a| < 2^(m-1)`: `|Q_{k-1}| < 2^(m-1) + 2u <= 2^m`, since `p >= 2`.

So `|g + Q_{k-1}| <= 2^(m+1) - u`. Below `2^m` the spacing is at most u, so the rounding error
is at most `u/2`. On `[2^m, 2^(m+1)]` the representables are spaced `2u`, with `2^(m+1)`
included, so the error is at most u. Hence `|h_k| <= u`. ∎

### Step B: T(j), LA(j) for all j < k imply T(k), for k >= 2

Write `U = U_k`, `a = g_{k-1}`, `w = U_{k-1} <= U` (by F2), `b = Q_{k-2}`, and
`rho = Q_{k-1} - a = RN(a + b) - a = b - h_{k-1}`. Negating a and b negates rho (F3), so
assume `a > 0`.

**Lemma B: `|b| <= 2U`.** `b = S_{k-2} - H_{k-2}`. Lemma S gives `|S_{k-2}| < 2U`. LA(j) for
`j <= k-2` together with Lemma U gives `|H_{k-2}| < 2U / (2^p - 1) <= 4U / 2^p` (for `p >= 1`).
So `|b| < 2U + 4U/2^p`. Above the power of two `2U` the representables are spaced `4U/2^p`, so
`|b| <= 2U`. ∎

**Strict bound.** T(k-1) and (F1) give `|b| <= |g_{k-2}| + 2w < U + 2w`.

w is a power of two at most U, so exactly one of the following three cases applies.

- **Case `w <= U/4`.** LA(k-1) gives `|h_{k-1}| <= w`. Then
  `|rho| <= |b| + |h_{k-1}| < U + 3w <= 7U/4`.
- **Case `w = U/2`.** Here `a` lies in `[2^(m-2), 2^(m-1) - w]` and is a multiple of w, with
  `m = mag g_k`. The strict bound gives `|b| < 4w`, so `a - 4w < a + b < a + 4w`.
  - *Upper side.* If `a + 4w <= 2^(m-1)`, it is representable (F4), so `RN(a+b) <= a + 4w`.
    Otherwise `a + 4w` is one of three values:
    - `2^(m-1) + 2w`: representable.
    - `2^(m-1) + w`: the midpoint of `2^(m-1)` and `2^(m-1) + 2w`, so `RN(a+b) <= 2^(m-1)`.
    - `2^(m-1) + 3w`: the midpoint of `2^(m-1) + 2w` and `2^(m-1) + 4w`, so
      `RN(a+b) <= 2^(m-1) + 2w`.

    The strictness `a + b < a + 4w` is what excludes the even neighbour `2^(m-1) + 4w`.
    In every case `rho <= 4w = 2U`.
  - *Lower side.* `a - 4w` is a multiple of w with magnitude below `2^(m-1)`, hence
    representable, so `rho >= -4w = -2U`.
- **Case `w = U`.** Here `a` lies in `[2^(m-1), 2^m - U]` and is a multiple of U. Lemma B gives
  `a - 2U <= a + b <= a + 2U`.
  - *Upper side.* If `a + 2U <= 2^m`, it is representable, so `rho <= 2U`. Otherwise
    `a = 2^m - U` and `a + b <= 2^m + U`. That is the midpoint of `2^m` and `2^m + 2U`, and
    ties-to-even (F5) with monotonicity give `RN(a+b) <= 2^m`, so `rho <= U`.
  - *Lower side.* `a - 2U` is representable, so `rho >= -2U`.

In all cases `|rho| <= 2U`, which is T(k). Step A then gives LA(k). ∎

## Remarks

- The bound is tight: `|rho| = 2U` is attained (model), and `|h| = U` is attained in binary64
  (`LookaheadQEX.v`).
- Ties-to-even is used essentially in case `w = U`. Under round-half-away, `a + b = 2^m + U`
  would round to `2^m + 2U` and give `rho = 3U`.
- The full Priest gap is used in Lemma S, Lemma U and (F1). With gap `p - 1`, Lemma S fails
  (the `gapk.py` / `shrink.py` witness, ratio 5/2).
- The magnitude–lattice dichotomy is not needed. The lattice idea survives only in Lemma B, as
  the representable gap above `2U`. The `c = 5/4` observation (`dclimb.py`) is moot.
- Consequence for the invariant (`CascadeInvariant.v`): the N-step look-ahead is now
  `|h| <= ulp(g_next)` with `<` going to N and `=` going to T, as planned. This proof gives the
  `<=`. The N/T split and the P state are untouched.

## Rocq map

| paper | Rocq (`CascadeTailBound.v`) |
|---|---|
| (F1) keys | `chain_count`, `keys_derived` (counting, from Priest chains) |
| Lemma S | `tail_lt`, `chain_small`, `HS_derived` |
| Lemma U | `Tsum_bound` (division-free form) |
| Lemma B | `lemma_B` (with `gap`) |
| Step A | `stepA`, `LA_of_TB` |
| Step B cases | `TB_step` with `case_half_any`, `case_full_any`, `tie_even` |
| Theorem | `tail_bound_and_lookahead`, `cascade_tail_bound`, `cascade_closed_lookahead` |

## Not done

- binary64: the FLT format (underflow floor), the binary64 cascade
  `b64_grow_expansion_aux` and its correspondence with this FLX cascade.
- binary64 near underflow, where `ulp` becomes the FLT floor and the formulas above change.
- Zero components (at most one per chain, at the bottom), excluded by hypothesis.
