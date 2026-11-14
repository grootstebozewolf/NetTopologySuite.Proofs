<!-- doc-kind: finding
date: 2026-08-22
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Close #482 — Shewchuk half-ulp counterexample retip

**Type:** task · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** —

## Question

#482 asks that the `fast_expansion_sum_nonoverlap_shewchuk` headline be retipped
as a disproof of the *corpus* postcondition (half-ulp `strict_succ_b64`), not of
Shewchuk 1997 as published. Is that ask satisfied by the corpus today, and does
it close?

Audit evidence to verify, then cite:

- `docs/phase0-completion.md:93-113` already carries the retipped wording and
  links both the issue and the witness.
- `theories-flocq/B64_Shewchuk_Thm13_counterexample.v` — `nonoverlap_shewchuk_256_1_false`,
  `e_nonoverlap`, `f_nonoverlap`, `inputs_sum_eq`, all Qed.
- Registered in `docs/admitted-counterexamples.txt:119-142` and
  `docs/audit-exceptions.txt:106-113`.
- `b64_orient2d_exact_sound` untouched; the restricted true form lives in
  `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`.

Decide also whether the one gap the audit noticed — the counterexample has no
`docs/verified-claims.md` row, living only in the two registries — is part of
this ask or a separate micro.

## Resolution

**Closed 2026-08-22. #482 is satisfied by the corpus; closed with the evidence
comment. The claims-register gap is a separate micro, filed as #503.**

Every item of the ask verified against the tree:

- **The retip is in place**, `docs/phase0-completion.md:93-102`, in the wording
  the issue asked for — "false as stated: a disproof of the **corpus**
  postcondition (half-ulp `strict_succ_b64`), not of Shewchuk 1997 as published".
  Lines 105-109 also record that Slice A did not close the headline and that the
  statement in `B64_FastExpansionSum_Shewchuk.v` is archived false-as-stated.
- **Five Qed lemmas**, not the four the audit listed:
  `strict_succ_b64_256_1_false:92` as well as
  `nonoverlap_shewchuk_256_1_false:108`, `e_nonoverlap:130`, `f_nonoverlap:152`,
  `inputs_sum_eq:171`.
- **Restricted true form** `fast_expansion_sum_nonoverlap_shewchuk_int_safe_two_pairs`
  Qed in `B64_FastExpansionSum_Shewchuk_Route2.v`.
- **Both registries** carry it, with the counterexample registry naming the
  achievable route (weaken to Shewchuk's bit-disjoint predicate, re-aim O1–O8)
  and recording `RESOLVED-VIA-ABORT 2026-06-24: no longer Admitted`.
- **"What stays" honoured**: `b64_orient2d_exact_sound` untouched and still
  consumed at `theories-flocq/Shewchuk_vs_Z2.v:124`; no upstream issue filed.

**On the claims-register question — it is a real gap, but not this ask's.** The
decisive test was whether the corpus treats machine-checked negatives as citable
claims at all. It does: `hobby_lemma_4_3_no_proper` sits in the counterexample
registry *and* carries a `verified-claims.md` row marked "**Refuted:**", and
`inner_offset_past_center_not_at_distance` carries two rows. So refutations are
citable by convention and this one is the exception. #482's ask was a doc retip,
so the row belongs to a separate micro (#503), which also records why the
omission was invisible: `scripts/validate-claims.sh` checks claims → source, but
nothing checks source-negative → claims.
