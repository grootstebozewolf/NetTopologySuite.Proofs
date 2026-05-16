# Category C policy — per-theorem axiom footprint

**Status**: Draft, pending decision.
**Origin**: May 2026 axiom-leak investigation. Empirical artefacts and
slice 1 of the parametric-architecture refactor referenced below.

## 1. Summary

The corpus's README documents three permitted axioms
(`ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`,
`FunctionalExtensionality.functional_extensionality_dep`). The May 2026
investigation found that 74 per-theorem `Print Assumptions` outputs across
12 files in `theories-flocq/` pull a fourth axiom,
`Classical_Prop.classic`, inherited transitively from Flocq's binary
arithmetic operations. This document records the empirical findings,
the architecture limit they reveal, and the policy options for
reconciling the corpus with its documented axiom claim.

The policy this document is for: **which theorems may exist in the
corpus with `Classical_Prop.classic` in their per-theorem PA closure,
and how is that exception managed**.

This document does not prescribe a choice. It scopes the trade-offs
honestly and names what evidence the decision still needs.

## 2. How the leak was discovered

The trigger was a `coqchk -silent -o` invocation during the
`Validate_binary64_bridge.v` work that showed four axioms in the union
closure: the three README-documented plus `Classical_Prop.classic`. The
README intro (lines 18-29) claims three; the README later (lines 405+)
references "4-axiom set" repeatedly. The two are internally
inconsistent.

A bisect against the `coqchk -o` union showed `classic` was present
from the **second commit ever** in the repo (`96eced2`, 2026-05-14). At
that commit, per-theorem `Print Assumptions` outputs in
`theories/Distance.v` and `theories/Orientation.v` showed only three
axioms — consistent with the README intro's claim. The
union-closure-vs-per-theorem disagreement is structural: `coqchk -o`
surfaces axioms from the entire Stdlib import closure including
lemmas the corpus doesn't use; per-theorem PA traces only axioms the
specific theorem's term references.

The per-theorem audit (sequential `make -j1` build with PA-block-to-file
attribution) confirmed that at HEAD prior to slice 1, **74 theorems
across 12 `theories-flocq/` files** had `classic` in their per-theorem
PA closure. Zero `theories/` files were affected — the leak is entirely
through Flocq's binary arithmetic.

## 3. Where `classic` actually enters

Three independent probes, verbatim outputs preserved in the commit
history of `946a0d4`:

```
Print Assumptions Binary.Bminus.   -> 4 axioms incl. Classical_Prop.classic
Print Assumptions Binary.Bmult.    -> 4 axioms incl. Classical_Prop.classic
Print Assumptions Binary.Bplus.    -> 4 axioms incl. Classical_Prop.classic
Print Assumptions Binary.B2R.      -> 2 axioms; NO classic
Print Assumptions Binary.is_finite.-> Closed under the global context
Print Assumptions Binary.Bcompare. -> Closed under the global context
Print Assumptions Generic_fmt.round. -> 4 axioms incl. classic
Print Assumptions Binary.Bcompare_correct. -> 4 axioms incl. classic
```

Two distinct contamination chains:

- **Type-level (C1)**: any theorem whose *type* mentions
  `Binary.Bminus` / `Bmult` / `Bplus` (directly, or via aliases
  `b64_minus` / `b64_mult` / `b64_plus`, or via compositions
  `b64_cross` / `b64_dist_sq` / `b64_orient2d`) inherits `classic`
  through type-checking. The closure is computed off the type — no
  proof reformulation can eliminate the inheritance.

- **Proof-level (C2)**: a theorem whose type *does not* mention any of
  the above operations can still pull `classic` if its *proof* applies
  a Flocq lemma whose own closure pulls `classic`. The canonical
  example is `Bcompare_correct`, which relates `Bcompare`'s integer
  result to `Rcompare` on the operands' R-projections. The relation
  itself is classically proved upstream in Flocq.

These are structurally different leaks and require different fixes.

## 4. Per-theorem categorisation

For every theorem with `classic` in its PA output, the leak falls
into one of:

| Cat | Type tainted? | Proof tainted? | Cleanable via | Example |
|-----|--------------|----------------|---------------|---------|
| A | no | no | Already clean if it's in a clean file; if in a tainted file, can be exposed via parametric `Section` lift | `greedy_simplify_preserves_head` (slice 1) |
| B | yes | yes | Removal + verification of inline-provability at consumer sites; trivial structural content | `greedy_simplify_binary64_never_none` (slice 1; restored as documented C, see §6) |
| C1 | yes | (irrelevant) | Structural refactor of the underlying definitions: parametrise `b64_orient2d` / `b64_cross` / etc. over abstract operations, so the type doesn't mention Flocq's concrete operations | `b64_orient2d_finite_of_safe` (mentions `b64_orient2d_safe`, which mentions `b64_round`) |
| C2 | no | yes | Tactical re-proof avoiding the classic-tainted Flocq lemma. Depends on whether a non-classic alternative exists | `b64_le_R_of_true` (type only mentions `is_finite`, `b64_le`, `B2R`, `<=`; classic enters via `rewrite Bcompare_correct`) |

The category labels are descriptive, not prescriptive — they describe
*how* the contamination got in, not whether the theorem deserves to
exist.

## 5. Slice 1's evidence

Commit `b010037` refactored `Validate_binary64.v`'s 13 lemmas into a
parametric architecture:

- 3 abstract structural lemmas (`greedy_simplify_preserves_head`,
  `_aux_length_le`, `_aux_in_kept`) now show
  `Closed under the global context` — zero axioms.
- 1 Category C1 theorem (`greedy_simplify_binary64_never_none`) was
  initially removed (treating it as Category B), then restored after
  review identified the removal as motivated reasoning rather than
  evidence. It now lives in the file with an explicit `(* CATEGORY C *)`
  block documenting why its content cannot be lifted to the abstract
  layer.

The slice demonstrates:
- The parametric-`Section` lift works for Category A theorems.
- It does not lift Category C1 content; attempts to do so collapse
  the theorem to a tautology of the option / boolean / list type that
  no longer says anything specific about the concrete function.
- It does not address Category C2; the proofs are not in the section's
  view.

Slice 1's classic count: 74 → 71 (3 cleared, all Category A).

## 6. What this corpus's "axiom-free" claim is actually about

The README's intro states the claim about per-theorem `Print
Assumptions` outputs. The investigation has established that this
claim, taken at face value, is currently violated by 71 theorems.

The natural follow-up — "is the claim *as stated* achievable?" — has a
qualified answer:

- For Category A theorems, yes. The parametric architecture clears
  them.
- For Category B, yes (with documentation). The trivial content is
  not lost; consumers inline a one-line proof.
- For Category C2, **possibly** — depends on whether non-classic
  alternatives exist in Flocq for each tainted lemma. Empirically
  untested across the corpus.
- For Category C1, **no, not while using Flocq's binary arithmetic**.
  The `Binary.Bplus` / `Bminus` / `Bmult` definitions are the leak
  source; any theorem whose type references them inherits `classic`.
  Eliminating C1 requires either replacing Flocq's operations with a
  classic-free alternative (a major upstream contribution) or
  restating every binary64 theorem so its type does not name the
  concrete operations (in which case the theorem stops being a
  statement *about* those operations).

This is the architectural limit. It is intrinsic to using Flocq as
the binary64 model.

## 7. Policy options

Three legitimate policy positions for the corpus, with different
trade-offs.

### Option 1 — strict claim, no concrete-operation theorems

The README claim is taken literally for every theorem the corpus
ships. Files leave `audit-exceptions.txt` only when every theorem in
the file is classic-clean (Category A or B). Category C1 theorems
cannot ship — they are removed or rewritten parametrically (losing
the content, in the C1 case).

**Pros.**
- Mechanically enforceable. The audit script can stay file-level.
- The README's text is true literally.

**Cons.**
- The corpus loses its ability to state theorems *about* `b64_orient2d`,
  `b64_cross`, `b64_dist_sq`, `b64_intersect_*`, and every other
  composition of Flocq's binary arithmetic.
- The downstream consumers in `.Curve`, the OCaml oracle, and any
  paper-cited results lose the named-theorem documentation of those
  functions' contracts.
- Effectively rules out the Flocq-based formalisation pattern this
  corpus is built on.

### Option 2 — strict claim, per-theorem exception registry

The README claim is upheld for every theorem **not** in an explicit
registry. Category C theorems live in
`docs/category-c-registry.txt`, each with a justification block in
the source file naming why the theorem's content cannot be cleaned.
The audit script is extended to support per-theorem (not just
per-file) exceptions.

**Pros.**
- The README's text stays accurate **for the theorems not on the
  registry**, which is most of the corpus.
- The registry is auditable: each Category C entry is a deliberate
  decision with documented reasoning, not a silent contamination.
- Mixed files (some clean, some Cat C) can have the clean theorems
  audited while the C theorems sit on the exception.
- Composable with future cleanup: when a Flocq update or upstream
  contribution makes a C theorem cleanable, it leaves the registry.

**Cons.**
- The README needs a one-sentence pointer to the registry. Without
  that pointer the intro is still misleading.
- The audit script needs ~50 more lines to do PA-block-to-theorem
  matching (positional, against the source file's ordered
  `Print Assumptions <name>.` calls).
- Every Category C theorem the corpus already ships requires a
  classification pass to be moved onto the registry.

### Option 3 — corrected claim, no registry

The README is updated to say: "the corpus's own files do not
introduce new axioms; the four-axiom set
(`sig_not_dec`, `sig_forall_dec`, `functional_extensionality_dep`,
`Classical_Prop.classic`) is inherited from Flocq's binary
arithmetic operations and is documented as such." The audit-exceptions
list becomes the deprecation runway for transitional contamination
that can be cleaned (Category A leaks that haven't been refactored
yet, plus C2 leaks that have a clean alternative). Category C1 is
acknowledged as inherent.

**Pros.**
- The README matches reality.
- The architectural limit is named, not papered over.
- The corpus retains its ability to state theorems about Flocq's
  operations directly.

**Cons.**
- Updates the README. The current direction (May 2026) has been
  explicit that the README should not be updated — it is the spec
  the corpus should match, not the artefact that adapts to drift.
- The corpus's distinguishing claim weakens from "three axioms" to
  "four, one inherited from Flocq". For some readers (academic
  citers, downstream consumers comparing to other formalisations),
  this matters.

## 8. Open inputs the decision still needs

Per the May 2026 discussion that scoped this document, four pieces
of evidence would sharpen the policy choice:

1. **Full A/B/C1/C2 distribution.** A classification pass on every
   currently-tainted theorem (estimated 95 PA-audited entries across
   12 files; 76 of those pull `classic`). The C1:C2 ratio determines
   how much leverage tactical re-proof has versus structural refactor.
   Not done. Sample-based estimation suggests C1 dominates, but the
   sample size is small (one theorem inspected per file).

2. **Representative C theorem from each file** with a paragraph on
   what each theorem documents (its operational content) and what a
   parametric reformulation would lose. The input that lets us reason
   file-by-file about whether documentation value warrants exception
   status. Not done.

3. **README intent**: per-theorem closure exactly equal to the three
   axioms (Option 1 or 2), or "corpus does not introduce axioms,
   inheritance is acknowledged" (Option 3). This is a project-author
   decision, not derivable from empirical evidence.

4. **C# port (`NetTopologySuite.Curve`) implicit-dependency audit**:
   whether the C# port consumes any extracted Coq function under an
   assumption (totality, finiteness, never-None, etc.) that a named
   theorem in this corpus is currently documenting. If yes, removing
   those theorems (Option 1) removes the C# port's justification for
   its handling. The slice-1 partial check on
   `greedy_simplify_binary64_never_none` found no C# dependence on
   that specific theorem, but the broader audit hasn't run.

## 9. What this document does not decide

- It does not set the allowlist. The current `docs/axiom-allowlist.txt`
  lists three axioms, matching Option 1/2's stricter posture, but is
  trivially editable to four for Option 3.
- It does not implement the per-theorem registry. The audit script
  currently supports file-level exceptions only.
- It does not authorise reverting any of the contaminated theorems.
  Slice 1 is committed and live; the rest of the corpus is in its
  pre-investigation state.

## 10. Smallest concrete next step depending on choice

- **Option 1**: nothing more is needed at the corpus level. The
  parametric-architecture refactor across the remaining 11 files
  (4-8 hours of focused work, depending on the C1 share) closes
  Category A leaks; Category C1 theorems get removed; the audit
  flips to "all green when refactor completes." Loss of stated
  contracts on Flocq operations is the cost.

- **Option 2**: extend `scripts/audit_axioms.sh` to do positional
  PA-block-to-theorem matching against the source file's
  `Print Assumptions <name>.` ordering; create
  `docs/category-c-registry.txt`; classify the 71 currently-tainted
  theorems into A/B/C1/C2 and populate the registry. A few hours of
  diagnostic work + the script extension; no theorem refactors yet.

- **Option 3**: update README lines 18-29 to acknowledge the
  inherited `Classical_Prop.classic`; update
  `docs/axiom-allowlist.txt` to four entries; the audit's
  `audit-exceptions.txt` becomes only the deprecation runway for
  *cleanable* drift (no entries needed for inherent inheritance).
  The slice-1 work and the guardrail commits stay as they are; their
  meaning shifts from "fixing leaks" to "cleaning up drift while
  documenting inheritance."

The smallest concrete next step in *any* case is committing this
document and pausing the refactor cadence until the choice is made.

---

*This document represents the corpus's understanding at commit
`946a0d4`; it does not predict where Flocq, Stdlib, or the corpus's
needs evolve from here. Future revisions should record the choice
made and the date.*
