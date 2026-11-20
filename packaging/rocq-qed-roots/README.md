<!-- doc-kind: guide -->
# rocq-qed-roots

| | |
|---|---|
| What | Kernel-checked real-root certificates for univariate polynomials, from rational coefficient enclosures to an exact conclusion. Booleans over Q decided by `vm_compute`; floating point never enters. |
| Chain | `qedinterval → qedpoly → qedroots → qedanalytic → qedjensen → RH experiments`; this package is the `qedroots` layer and ships `qedpoly` / `qedinterval` inside it until a second consumer needs them alone. |
| Programme | Not "formalize RH": the minimal verified substrate on which finite RH-adjacent statements are stated, computed and kernel-checked; each rung ends in QED or QEX. Hunt: `docs/attacks/2026-11-20-jensen-hyperbolicity-certificate.md`. |
| Deps / axioms / license | Stdlib only; BSD-3-Clause. `sig_not_dec`, `sig_forall_dec`, `functional_extensionality_dep` (stdlib classical reals). No `Admitted`. |
| Logpath | `NTS.Proofs` (decided 2026-11-20): kept for continuity with the corpus and the sibling packages, so vendored files build unmodified. |
| Build | `./assemble.sh` (vendor from MANIFEST), then `make && make install`, `opam install .`, `dune build` or `nix-build`; `make package` writes the opam tarball. |

| Module | Contents | Headline |
|---|---|---|
| `QedPoly` | `peval`, `lead`, `prodlin`, synthetic division, continuity, formal derivative; Q-side `pmulQ`, `peqQ`, `pderivQ` with Q2R transport | `factor_from_roots`, `peval_Q2R_pmulQ`, `peval_derivable` |
| `QedInterval` | `box` of rational coefficient intervals, enclosure `ieval` (tight; tightness unproved), strict sign `isign`, `in_box` (the interface `qedanalytic` must produce), box derivative | `ieval_sound`, `isign_mul_neg`, `in_box_pderiv` |
| `QedRoots` | `hyperbolic` (root multiset) vs `simple_real_rooted` (distinct, all zeros), separate definitions; `box_cert` (robust sign alternation), `factor_cert` (exact multiplicities) | **`cert_sound`**, `cert_roots_in_gaps`, **`factor_cert_sound`** |
| `QedRootsRefute` | Laguerre form `p′² − p·p″ ≥ 0` for hyperbolic p; `lag_box_cert` (enclosed upper bound < 0 at one rational point refutes the whole box) | **`laguerre_hyperbolic`**, **`lag_box_cert_sound`**, `lag_box_cert_of_quadratic_neg_disc`, `box_cert_lag_exclusive` |
| `QedRootsExamples` | P5 = 6+41X+97X²+97X³+41X⁴+6X⁵ accepted on ±1/20; P5up (P5 with constant term 9) refuted on ±1/2; `beta_box` negative control; repeated roots via factors; negative controls | `P5_neighbourhood_simple_real_rooted`, `P5up_neighbourhood_not_hyperbolic`, `double_root_box_uncertifiable`, `beta_box_lag_never` |

| Point | Statement |
|---|---|
| Accept | `in_box p b → box_cert b xs = true → simple_real_rooted p`, for every real p in the box. |
| Refute | `in_box p b → lag_box_cert b x = true → ¬ hyperbolic p`; for point boxes with rational coefficients, a negative discriminant always passes at the vertex; on proper boxes it can fail even in degree 2 (`beta_box_lag_never`). |
| Repeated roots | `box_cert` can never accept one (`double_root_box_uncertifiable`); `factor_cert` expresses them as repeated factors. |
| Non-vacuity | Both checkers require `box_wf` (lo ≤ hi), so a passing box is inhabited (`box_cert_inhabited`, `lag_box_cert_inhabited`). |
| Completeness | Not claimed. A failed check proves nothing; accept and refute never both pass on overlapping boxes. |
| OPEN | Sturm / Cauchy index, squarefree decomposition, refutation complete beyond degree 2. |
