<!-- doc-kind: finding
date: 2026-11-20
Provenance: a0411a057fc5fdc8e0c76bcf55324e423b1cb7fe
Theorems: `QedRootsRefute.v : lag_box_cert_of_quadratic_neg_disc`, `QedRoots.v : cert_roots_in_gaps`, `QedRootsExamples.v : x2_plus_one_not_hyperbolic`
Supersedes: docs/attacks/2026-11-20-jensen-hyperbolicity-certificate.md
-->
# Follow-up: degree-2 checker completeness and isolating gaps

Records the review corrections on the qedroots certificate at
`a0411a057fc5fdc8e0c76bcf55324e423b1cb7fe`. The parent ticket stays the
write-up of the sign-alternation and Laguerre proofs.

`lag_box_cert_of_quadratic_neg_disc` states that rational `a`, `b`, `c`
with `~ (c == 0)` and `b² − 4ac < 0` make
`lag_box_cert (point_box [a; b; c]) ((- b) / ((2 # 1) * c))` true.
The division is `Qdiv`, used only under that `Qeq` side condition.
`cert_roots_in_gaps` is the same `box_cert` witness, with one root
strictly inside each open sample gap and the factorisation identifying
those roots as all of the real zeros.

`x2_plus_one_lag_cert` and `x2_plus_one_not_hyperbolic` are the
lowercase names of the `X²+1` controls. Headline `Print Assumptions`
commands now sit in the five `.v` files.

No Flocq coefficient enclosure, no Sturm or Cauchy index, no Jensen
coefficient, and no Davenport–Heilbronn run are in this follow-up.

SUMMARY ok=2 warn=0 bug=0

OUTCOME: QED for the rational quadratic boolean certificate and for the
isolating-gap export. Sturm, squarefree search, Flocq `in_box`, and the
Davenport–Heilbronn control stay QEX.
