<!-- doc-kind: guide -->
# RocqRefRunner JTS ↔ NTS equivalence

The catalyst is NTS. JTS already ships a Java reconstruction of the
certified integer-domain orientation sign (`RocqRefRunner.refSign`,
JTS #1106 / fork SoT `feature/sfa-curve-rgr`). This slice ports that
**reference** to NTS and proves the two ports compute the same
function.

Call it **RocqRefRunner**, not “oracle”. The subprocess `oracle_bin`
is a different boundary (extracted kernel, line protocol). Production
`Orientation.index` (double-double) is a third thing and is **not**
claimed sound here.

## What is proved

In [`theories/RocqRefRunner.v`](../theories/RocqRefRunner.v):

| Theorem | Meaning |
|---|---|
| `rocqref_refSign_eq_cross` | `Z.sgn` of the integer 2×2 determinant is the exact `cross` sign of the embedded points |
| `rocqref_idet_fits_int64` | on `|coord| ≤ 2²⁵`, `|det| ≤ 2⁵³ ≤ 2⁶³−1`, so Java/`C#` `long` is an exact evaluator |

The formula is the one both ports implement:

```
det = (p1x - p0x) * (qy - p0y) - (qx - p0x) * (p1y - p0y)
sign = sgn(det)    # -1 CW, 0 collinear, +1 CCW
```

That is also `theories/Orientation.v` `cross` after `IZR` embedding.

## What the port gate checks

[`oracle/rocqref/jts_nts_equiv_vectors.txt`](../oracle/rocqref/jts_nts_equiv_vectors.txt)
is the shared corpus. [`oracle/rocqref/check_jts_nts_equiv.py`](../oracle/rocqref/check_jts_nts_equiv.py)
recomputes the Qed formula and rejects a stale expected sign.

Consumers load the same file:

- JTS `RocqRefRunner.loadProofCases` + `RocqRefRunnerTest`
- NTS `RocqRefRunner.LoadProofCases` + `RocqRefRunnerTest`

A green run means: Java `refSign`, C# `RefSign`, and the Coq `rocqref_refSign`
agree on every exported integer triple. It does **not** mean NTS
`Orientation.Index` is verified.

## Relation to Phase 5 / `libntsrocq`

Orthogonal. Phase 5 is the in-process extracted kernel. RocqRefRunner
is the integer-domain *reference reconstruction* used as a test
oracle for #1106-style soundness pins. Do not flip production noding
onto either.
