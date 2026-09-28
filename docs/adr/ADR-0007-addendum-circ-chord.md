# ADR-0007 addendum — Circ × chord (2026-09-28)

| Field | Value |
|---------------|--------------------------------------------------------------|
| **Order** | ADR-0007 addendum |
| **Status** | **Proposed** until BDFL accepts it |
| **Parent** | ADR-0007 stays **Accepted** |
| **Date** | 2026-09-28 |
| **Deciders** | Joost (BDFL); proposed by Jeroen Bloemscheer |

This addendum does not rewrite the Decision of ADR-0007. It names one pairwise oracle. It does not merge until Joost accepts it. The `I_ok` change that makes the tree match this text is a separate pull request and stays unmerged until then.

**Span.** A circular egg carries `circ_theta0` and `circ_sweep`. Intake does not compute them. The sheet is the carrier. A partial arc with no supplied span is Intake Decline. `|circ_sweep| = 2π` is a full circle and is not this oracle.

**𝓘(circ, chord).** For `0 < |Δθ| < 2π`:

- **Hit** `(p, ti, tj)` when some `ζ` is a `zeta_seg_hit` on the egg's own chart: `p` is the chart point at the egg pole, `ti = t_of_zeta`, `tj = tj_of`. The witness on main is `host_circ_chord_hit_ok`.
- **Empty** when no such `ζ` exists.
- **Decline** only for a full circle or a zero sweep.

A second crossing is not a second `IResult` arm. Split the chord at the rational foot and cook each half once. `LoopDischarged`, `CircGamma`, and any new oracle keyword stay fenced. `classify_zeta_Z` sits below this statement. It is not a precondition of the amendment.

**NURBS.** The fail-closed `MkNurbs` arm already on main is the year-1 constructor. Exact NURBS×NURBS is year 2. This sentence is the #873 ratification, not a second process.

**Not this letter.** Flatten, the clothoid track, F5, and C1.4–C1.12.
