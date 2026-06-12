# ADR-0001 — Stack and licence path for Fresnel internalisation (route D)

| Field         | Value                                                        |
|---------------|--------------------------------------------------------------|
| **Order**     | ADR-0001 (first ADR of this corpus; establishes the format)  |
| **Status**    | **Accepted** — approved by Joost (BDFL), 2026-06-12          |
| **Deciders**  | Joost (BDFL)                                                 |
| **Date**      | 2026-06-12                                                   |
| **Superseded by** | — (none). If a later ADR changes this decision, set this field to its number and flip Status to *Superseded*. |

Status lifecycle for this and future ADRs: *Proposed → Accepted /
Rejected → (possibly) Superseded*. ADRs are numbered in approval-request
order and never renumbered; a superseded ADR stays in the tree with its
pointer updated.

---

## Context (self-contained)

NetTopologySuite.Proofs is a BSD-3-Clause corpus of Rocq/Coq proofs that
accompanies (but does not verify the implementation of) NetTopologySuite.
Its axiom policy is a three-axiom allowlist (`sig_not_dec`,
`sig_forall_dec`, `functional_extensionality_dep` — the cost of Stdlib's
classical reals), with two documented exception lanes where
`Classical_Prop.classic` additionally enters:

1. the **Flocq lane** (`theories-flocq/`), structurally via Flocq's
   binary-operation proofs (Flocq is an external LGPL Inria library the
   corpus already depends on and pins in CI), and
2. the **Category-C R-side lane** (`theories/Atan2.v`,
   `AngleBetween.v`, `ArcLength.v`, …), via Stdlib's `atan`/`sin_lt_x`
   proofs; each file carries an entry in `docs/audit-exceptions.txt`.

The clothoid verification ladder
(`docs/clothoid-open-questions-triage.md`) is now fully climbed except
**route (D): full Fresnel internalisation** — defining the clothoid
moment integrals P/Q inside the corpus and proving the analytic facts
(differentiation under the integral, monotone-branch behaviour) that
`ClothoidResidual.v` currently takes as *named Section hypotheses*. Those
hypotheses are externally witnessed Qed in **clothoid-halley-coq**, a
public EUPL-1.2 repro whose proofs are written against **Coquelicot**
(Inria's LGPL analysis library on top of Stdlib reals), and whose README
contains an integration note offering the proofs to this corpus.

Route (D) is currently marked *pivot-away* because it is gated on three
scope decisions (triage §5.1) that belong to the BDFL, not to a working
session: which analysis stack to use, what the axiom bookkeeping is, and
whether any EUPL text may enter the BSD-3 tree. This ADR asked for those
decisions; with acceptance, route (D) reclassifies from *BDFL-gated* to
*consumer-gated*: still not scheduled until a downstream consumer
demands end-to-end machine-checked Halley, but executable without a
policy stall when one does.

## Decision (the choice being proposed)

**Adopt Coquelicot as a second pinned external library dependency,
confined to a new lane (`theories-coquelicot/`), with freshly authored
BSD-3 proof scripts; do not copy EUPL-1.2 text into the tree; keep the
three-axiom allowlist unchanged and absorb any additional classical
axioms through the existing per-file `docs/audit-exceptions.txt`
mechanism; keep route (D) consumer-gated.**

Concretely, when a consumer triggers route (D):

1. P/Q are defined with Coquelicot's `RInt`, and the analytic facts are
   proved using its `auto_derive`/parametric-integral machinery — the
   path the external witness has already shown closes in days, not
   weeks.
2. All scripts are written fresh for this corpus under BSD-3-Clause.
   The EUPL witness is consulted as a reference and cited in headers
   (as it is today), but no script text is adopted verbatim; the
   licence boundary stays file-system-clean.
3. The new lane mirrors the Flocq lane operationally: pinned version in
   the CI container and the host-fallback doc (Coquelicot, like Flocq,
   is installable from the `coq-released` opam repo and source-buildable
   from Inria GitLab when that repo is network-blocked), per-file
   `audit-exceptions.txt` entries for whatever classical axioms the
   `RInt` layer pulls, and `Print Assumptions` footers on every theorem.
4. `ClothoidResidual.v` itself does not change: routes only *discharge*
   its hypotheses. The conditional three-axiom interface remains the
   citable artefact for consumers who do not want the heavier lane, and
   the differential oracle remains differential — never the source of
   truth.

## Consequences

**Positive.**
- Route (D) becomes executable on demand with a known cost (the witness
  repo demonstrates the proofs close in Coquelicot; the "3–5 day
  mechanical" estimate applies to this stack and to no other).
- The licence question dissolves rather than being adjudicated: no
  copyleft text enters the tree, so no per-file licence mixing, no
  reliance on interpreting the witness README's grant note.
- The allowlist stays at three axioms; axiom hygiene continues to be
  enforced by the existing audit (`audit_axioms.sh` + exceptions file)
  rather than by a policy amendment.
- Precedent-consistent: the corpus already pins one Inria LGPL library
  (Flocq) and already runs a documented `classic` exception lane; this
  adds a parallel lane, not a new kind of thing.

**Negative / accepted costs.**
- A second external dependency to pin, cache, and track across Rocq
  releases (Coquelicot's release cadence has historically lagged Rocq
  major bumps; the CI container isolates this, but upgrades get harder).
- A new lane fragments the corpus further (three proof dialects:
  Stdlib-R, Flocq-b64, Coquelicot-analysis). Reviewers need to know
  which lane a file lives in; the audit-exceptions file grows.
- Fresh authorship is slower than verbatim adoption (days rather than
  hours, since the witness scripts cannot be pasted), and carries
  transcription risk — mitigated by differential checking against the
  witness's statements.
- The lane will pull `classic` (and possibly Coquelicot-specific
  classical choice principles) into R-side files that are not atan/sin
  lineage; the exceptions file must say so honestly per file.

**Neutral / unchanged.**
- Nothing is scheduled by this ADR; the consumer gate stands.
- The corpus remains a companion (proofs about models), not a verified
  implementation; Q2's transcendental honesty boundary is unaffected.

## Alternatives not selected

- **(i) Stdlib `RiemannInt` internalisation.** Rejected as dominated:
  Stdlib has no parametric-integral differentiation lemma, so the
  genuinely hard analytic content must be built by hand (well beyond
  the mechanical estimate), *and* Stdlib's `RiemannInt`/MVT machinery
  pulls `Classical_Prop.classic` anyway — the same axiom cost as the
  selected option at several times the effort, with no dependency saved
  that matters (Stdlib-only purity is already broken by the Flocq lane).
- **(iii) Verbatim adoption of the EUPL-1.2 witness scripts.** Rejected
  on two grounds: it does not avoid the Coquelicot dependency (the
  witness is written against Coquelicot, so (iii) implies (ii)'s
  dependency while adding a licence question), and it puts copyleft
  text inside a BSD-3 tree on the strength of a README integration
  note — defensible, but permanently explanation-bearing. Fresh
  authorship costs a few days and keeps the tree single-licence.
- **(0) Hold the conditional idiom forever (never take route D).**
  Not selected as a *recorded permanent* position, but its operational
  content is retained: the consumer gate stands, and the conditional
  interface + external witness + differential oracle remains the
  default citable combination. This ADR only removes the policy stall
  for the day the gate opens.

## Supersession note

None. This is the corpus's first ADR; it has not been superseded. Any
future ADR that changes the stack choice, the licence stance, or the
axiom bookkeeping for route (D) must reference this number, set the
field above, and flip the status to *Superseded*.
