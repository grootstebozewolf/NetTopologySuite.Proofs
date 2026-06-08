# Shewchuk Theorem 13 — §4.A re-derivation (gating prompt)

**Branch target:** `feat/4A-verify-rgr`

**Goal.** Settle one decision gating O1 cascade integration:

> Does the pathB trigger fire only when `compress (rev cs_output) = nil`?

**Beachhead lemma (target, prove or refute):**
`pathB_fires_only_when_output_compressed_empty`.

**Evidence required.** 2–3 `vm_compute` cascade traces on concrete cross-sign
`nonoverlap` inputs (e.g. `e=[2^60;1]`, `f=[-2^60]`), recording
`(cs_carry, compress (rev cs_output))` per pathB step.

**Output.** A decision:

- **Resolution-1:** empty output ⇒ `head_replace` discharged by `B2R a'=0` /
  empty disjunct only.
- **Resolution-2:** need a new `cs_carry`-dominates-output invariant clause.

**Stopping conditions.**

- FULL SUCCESS: decision documented + vm_compute witnesses landed in Coq.
- PARTIAL: decision documented, traces by hand only.
- COLLAPSE: traces contradict each other or contradict plan §7.

**Red-phase tangents (in order).**

1. Constant encoding for `2^60` / `-(2^60-2^8)` in Flocq `B754_finite`.
2. `compress` + `Rcompare` not fully `vm_compute`-reducible (use `length` / `B2R`
   proxies).
3. Sort order tie on `|2^60| = |-2^60|` (document which branch `insert_by_abs`
   takes).