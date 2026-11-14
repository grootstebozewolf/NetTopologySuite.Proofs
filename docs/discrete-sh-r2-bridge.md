<!-- doc-kind: guide -->
# Discrete → Sh(ℝ²) bridge — Boolean stalks, Heyting globe (2026-08-13)

topic: foundations
claimId: none
witness: none
mutation-seed: none

(ADR-0004 mint, explicit: this is a foundation lane — no oracle-facing
micro-kernel claim is minted, so the mutation/vacuity probe is intentionally
skipped, hence `claimId: none` / `witness: none`. For readers, the
documentation-level falsifier seed is `punct`, the punctured plane: EM fails
at its origin stalk (`heyting_em_fails`, `punct_stalk_not_boolean`), with the
non-open closed half-plane (`closed_halfplane_not_open`) as the
non-strict-predicate falsifier.)

**lane:** foundations · spatial-topos
**Modules**: [`theories/HeytingOpens.v`](../theories/HeytingOpens.v) ·
[`theories/PlaneConnected.v`](../theories/PlaneConnected.v) ·
[`theories/DiscreteShBridge.v`](../theories/DiscreteShBridge.v)
**Verdict**: **GREEN** — every stated theorem is Qed-closed on the
three-axiom classical-reals base. No `Admitted`, no new axioms, no registry
entries needed.

**Slogan proved**: the discrete (Boolean) logic of NTS predicates embeds
into the truth-value algebra Ω = O(ℝ²) of the spatial topos Sh(ℝ²);
**stalks of bridged values stay Boolean** at every point, while **globally Ω
is properly Heyting** (excluded middle fails); the pointwise semantics is
**sound in the spatial / well-adapted sense** — exact on the geometric
fragment, lax (and provably strictly lax) on implication and negation.

---

## §1 — Working level, stated honestly

We formalise the **subterminal fragment** of Sh(ℝ²), not sheaf categories:

- A *truth value over the plane* is an open subset `U : Point -> Prop`
  (`is_open`, metric balls). The frame O(ℝ²) of opens **is** the algebra
  of subobjects of 1 in Sh(ℝ²) — equivalently the global sections of its
  subobject classifier Ω. Everything is stated at this frame level.
- The *stalk of a truth value at p* is its germ at `p`. For an open `U`
  the germ collapses to plain membership
  (`DiscreteShBridge.v : open_germ_collapse`), and the germ of `¬U` at `p`
  says a whole neighbourhood misses `U`
  (`DiscreteShBridge.v : onot_germ_false`). "The stalk at `p` is Boolean"
  is the decidedness disjunction `stalk_boolean p U := U p ∨ (¬U) p`.
- **Not claimed**: no Grothendieck-topology machinery, no sheafification,
  no SDG infinitesimals/nilpotents, no full functor `Δ : Set → Sh(ℝ²)` as
  a functor between categories. The bridge is the truth-value component
  `bridge : bool → Ω` (plus the field form `pbridge : (Point → bool) → Ω`),
  which is exactly the part the NTS predicate corpus consumes.
- Equality of truth values is pointwise equivalence `osame` (no
  propositional extensionality — the corpus's axiom allowlist is
  respected; `Print Assumptions` blocks are in each file's footer).

**Kock / well-adapted reading.** For Kock–Reyes, a model is *well adapted*
when the embedding of the classical objects preserves the structure that
matters (finite limits, covers) and classical truth is recovered fibrewise.
The proved analogues here, per axiom family:

| Well-adapted axiom (informal) | Proved analogue |
|---|---|
| Embedding faithful/full on the discrete part | `bridge_injective`; `bridge_global_sections` + `stable_bool_field_constant` (Γ∘Δ = id on 2, Γ(Δ2) = 2) |
| Finite limits (meets) preserved | `bridge_andb`, `bridge_true_top` |
| Finite covers (joins) preserved | `bridge_orb`, `bridge_false_bot` |
| Logical on the Boolean core | `bridge_negb`, `bridge_implb` (negation/implication on the nose) |
| Classical truth recovered fibrewise ("spatial soundness") | `stalk_bridge_id`, `bridge_stalks_boolean`, `bridge_stalk_dec` |
| Site is spatial / enough points | `oincl_pointwise` (subobject order is pointwise) |

## §2 — The headline pair

**Stalks stay Boolean** (`DiscreteShBridge.v : discrete_bridge_headline`,
first half): for every `b : bool` and every point `p`, the stalk of
`bridge b` at `p` is decided (`bridge_stalks_boolean`), and decidably so
(`bridge_stalk_dec`). Evaluation at any point retracts the bridge
(`stalk_bridge_id`): the discrete logic survives fibrewise unchanged.

**Globally Ω is Heyting, not Boolean** (second half): the punctured plane
`punct = ℝ² \ {0}` is open (`HeytingOpens.v : punct_open`) but its stalk at
the origin is **not** decided (`punct_stalk_not_boolean`): the origin is
neither in `punct` nor in `¬punct` (no neighbourhood of the origin misses
the punctured plane, `onot_punct_empty`). Hence excluded middle fails in Ω
(`HeytingOpens.v : heyting_em_fails`) and double negation is strictly
above: `¬¬punct = ⊤ ≠ punct`
(`not_not_punct_top`, `double_negation_strict`).

That Ω *is* a Heyting algebra (so the failure is intuitionistic structure,
not a broken lattice) is `HeytingOpens.v : heyting_adjunction` — for open
`W`: `W ∧ U ⊆ V ⟺ W ⊆ (U ⇒ V)` — together with openness closure of all
operations (`open_and/or/ojoin/oimp/onot`) and the frame law
`oand_ojoin_distrib` (finite meets distribute over **arbitrary** joins).
The infinitary asymmetry that forces this shape: arbitrary joins of opens
stay open (`open_ojoin`) but the pointwise meet of the balls
`ball(0,r), r>0` is the non-open singleton `{0}`
(`infinite_meet_not_open`).

## §3 — The Boolean core is exactly the discrete image

Connectedness of the plane (`PlaneConnected.v : plane_connected`, by the
classical lub-walk along a segment — `completeness` of ℝ from the
three-axiom base, an explicit modulus of continuity `seg_continuous`,
nothing else) collapses the complemented elements of Ω to the two
constants:

- `complemented_is_discrete` — a complemented open is `⊤` or `⊥`;
- `discrete_iff_complemented` — complemented ⟺ in the image of `bridge`;
- `stalks_boolean_iff_discrete` — an open has Boolean stalks
  **everywhere** ⟺ it is discrete. (The punctured plane fails at exactly
  one point; that single bad stalk is what expels it from the Boolean
  core.)
- Field corollary `stable_bool_field_constant`: a pointwise-Boolean
  classification `f : Point → bool` of the plane whose two classes are
  both perturbation-stable (open) is constant. There is no non-trivial
  decidable, robust dichotomy of ℝ².

## §4 — Spatial soundness of pointwise evaluation

Evaluation at a point `p` (`stalk_at p`) against the Ω operations:

| Fragment | Behaviour | Theorem |
|---|---|---|
| `⊤ ⊥ ∧ ∨` and arbitrary `⋁` | preserved **exactly** | `stalk_sound_top/bot/and/or/join` |
| `⇒`, `¬` | sound but **lax** (topos-truth implies pointwise truth) | `stalk_lax_imp`, `stalk_lax_not` |
| `⇒` laxity is strict | pointwise implication the topos rejects | `stalk_imp_strict` (`punct → ⊥` at the origin: vacuously true pointwise, false in Ω) |
| entailment | pointwise semantics also **complete** for the order | `oincl_pointwise` |

This is the precise sense in which classical, point-by-point evaluation of
predicates (what the C#/JTS code does) is sound for the sheaf semantics:
it never disagrees on geometric content and never *loses* implications —
it can only accept implications that are not perturbation-stable.

## §5 — NTS-side instantiation: strict predicates are truth values

The OGC Interior-style strict predicates land in Ω; their non-strict
closures do not:

- `strict_halfplane_open` — `x < c` is open (via `dx_le_dist`, coordinate
  displacement dominated by distance);
- `open_disk_open` — the strict form of `Disk.v`'s `in_disk` is open, and
  sits inside the closed disk (`open_disk_incl_in_disk`);
- `HeytingOpens.v : closed_halfplane_not_open` — `x ≤ 0` is **not** open.

Reading for the robustness programme: a predicate has stable
(sheaf-semantic) truth exactly where it is locally constant under
perturbation. Strict comparisons are; boundary-inclusive ones are not —
their boundary points are precisely non-Boolean stalks. This is the formal
face of the corpus-wide preference for strict/interior forms in robust
branches (cf. the hot-pixel and snap-rounding lanes).

## §6 — WHAT IS QED-CLOSED / WHAT REMAINS OPEN

**Qed-closed** (all on the 3-axiom base; see `Print Assumptions` footers):
everything cited above — Heyting structure of O(ℝ²) with adjunction and
frame law; punctured-plane EM/double-negation failures; connectedness of
ℝ²; the bridge as injective logical embedding; Boolean-stalk headline and
its converse classification; spatial soundness table; strict half-plane /
open-disk instantiations.

**Open (candidate follow-ups, not blocking):**

- Nothing in this lane is deferred or conditional. Possible extensions:
  interpret a concrete NTS predicate family (e.g. orientation strictly-CCW
  as a function of one moving point) as an open via `pbridge`, connecting
  to `Orientation.v`;
- a Kripke–Joyal forcing reading of `oimp` on named geometry (the
  `heyting_adjunction` already gives the semantics);
- the same bridge over the segment-restricted subspace topology, to feed
  the overlay lanes.

## §7 — Relation to the corpus

- Consumes: `Distance.v` (metric API, `dist_lt_iff_dist_sq_lt`,
  `dist_pos_iff_distinct`), `Linearise.v` (`dist_triangle`), `Disk.v`
  (`in_disk`), `Real.v`.
- Consumed by: none yet (foundation lane). Natural consumers are the
  robustness/perturbation arguments (hot-pixel, snap-rounding) wherever
  "strict predicate ⇒ stable under perturbation" is currently re-derived
  ad hoc — that implication is `open_germ_collapse` + openness of the
  predicate.
- Branch: `claude/discrete-sh-r2-bridge-es8ad4`.

AI assistance disclosure: AI-drafted (Claude), human-reviewed.
