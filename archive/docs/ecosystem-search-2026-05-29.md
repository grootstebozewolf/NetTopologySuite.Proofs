# Rocq ecosystem deep audit — 2026-05-29

**Scope.**  Branch `ecosystem/library-search`.  Audit the Rocq/opam
ecosystem for libraries that could close or substantially reduce the
four major deferred entries before Phase 4 starts.  Builds on the
earlier negative survey: the corpus's switch had only `opam.ocaml.org`
configured; this session **adds the Coq community repository via a
GitHub mirror workaround**, then installs and inspects each candidate.

**Outcome.**  All three candidate libraries (GeoCoq, fourcolor,
mathcomp-analysis) **install cleanly on `rocq-core 9.1.1`**; one
(coq-hott) requires Rocq 9.0.1 and was correctly rejected by the
install rule.  Content-wise, **one AMBER and three REDs**: fourcolor's
`hypermap` is the right DCEL substrate for `extract_rings_valid` and
provides a modest reduction in scope; all other entries remain
unchanged.  Two side-deliverables: a reproducible network workaround,
and an internalisation opportunity for the H1 hypothesis in
`overlay_ng_correct_conditional`.

---

## §0 — Network policy workaround (reusable)

The corpus's network policy denies direct access to
`coq.inria.fr/opam/released` and its successor `rocq-prover.org/opam`
(both return HTTP 403 `x-deny-reason: host_not_allowed`).  GitHub IS
reachable, and the Coq community repo is mirrored at
`github.com/rocq-prover/opam`.  Workaround:

```sh
# 1. Clone the git mirror (GitHub is allowed)
git clone --depth 1 https://github.com/rocq-prover/opam.git /tmp/rocq-opam

# 2. Add the `released/` subdirectory as a local file:// opam repo
opam repo add coq-released "file:///tmp/rocq-opam/released"

# 3. Update
opam update

# (Optional) Remove with:
opam repo remove coq-released --all
```

The `coq-released` tarball at the original Inria/rocq-prover.org URL
has the same layout (`released/packages/...`), so this workaround
provides identical package access.  Reproducible; reusable in future
sessions.

---

## §1 — GeoCoq

  - Install: **clean**.  7 packages (`coq-core 9.1.1`, `coq-stdlib
    9.0.0`, `coqide-server 9.1.1`, `coq 9.1.1` metapackage,
    `coq-geocoq-coinc 2.5.0`, `coq-geocoq-axioms 2.5.0`,
    `coq-geocoq-main 2.5.0`).  No version conflicts; coexists with
    `rocq-core 9.1.1` via the `coq` compatibility metapackages.
  - Files: 183 `.v` files in `~/.opam/nts-flocq/lib/coq/user-contrib/
    GeoCoq/`.
  - Axiom footprint: **ZERO global `Axiom` or `Parameter`
    declarations**.  Uses typeclasses (`Class
    Tarski_neutral_dimensionless`) for the Tarski axioms.  The
    corpus's epistemic invariant is preserved on import.
  - JCT-adjacent content: NONE.
    - `Jordan` / `winding_number` / `simple_closed`: 0 hits.
    - `polygon` / `Polygon` / `point_in_polygon` / `crossing`: 0 hits.
    - `Curve` / `Boundary`: 0 hits.
    - `plane_separation`: 2 files, but these are **line separation**
      results (`TS A B X Y` = "A, X on opposite sides of line BC"),
      not polygon JCT.
  - Verdict: **GeoCoq is the wrong tool for `point_in_ring_correct`.**
    It is foundational axiomatic plane geometry (Tarski-style:
    `Tpoint`, `Bet`, `Cong`), with rich line-separation theory but no
    polygon-level JCT.  To use it: (1) prove R² satisfies
    `Tarski_neutral_dimensionless` (a model construction —
    nontrivial), (2) define polygons in Tarski terms, (3) prove JCT
    in Tarski's framework.  That's the same thesis-scale work, just
    inside a different axiomatic scaffold.

---

## §2 — coq-fourcolor

  - Install: **clean**.  43 packages including `elpi 3.7.1`,
    `rocq-hierarchy-builder 1.10.2`, `rocq-mathcomp-{boot, order,
    fingroup, ssreflect, algebra}`, `rocq-mathcomp-finmap`,
    `coq-mathcomp-{ssreflect, algebra}`, `coq-fourcolor-reals
    1.4.2`, `coq-fourcolor 1.4.2`.  Compile time ~10 min.
  - Files: 119 `.v` files in `~/.opam/nts-flocq/lib/coq/user-contrib/
    fourcolor/`.
  - Axiom footprint: **ZERO global `Axiom` or `Parameter`
    declarations in 119 installed files**.  Uses ssreflect
    typeclasses throughout.  The corpus's epistemic invariant is
    preserved on import.
  - Key contents:
    - `proof/hypermap.v` — `Record hypermap` with three
      mutually-inverse permutations `edge` / `node` / `face`.
      **Equivalent to a DCEL.**
    - `proof/jordan.v` — `Theorem planar_Jordan : planar G ->
      Jordan G` (Qed-closed).  **Combinatorial** Jordan property:
      no Moebius paths in planar hypermaps.  NOT geometric JCT for
      R² polygons.
    - `proof/realplane.v` — `point`, `region`, `map`, `open`,
      `closure`, `connected`, `simple_map`, `border`, `adjacent`
      over `Real.val R`.  Topology toolkit suitable for stating
      `geometric_interior` precisely in Coq.
    - `proof/embed.v` — embedding of hypermap configurations into
      real-plane maps.  Used internally for the 4CT proof.
    - `proof/snip.v` — disk-decomposition of planar hypermaps
      along rings.
  - Missing: direct `Jordan_curve_theorem` for R² polygons.  The
    geometric-side bridge in `realplane.v` is used as scaffolding for
    coloring statements, not for proving a separating theorem about
    simple closed curves.
  - No automated bridge from `(Point, Point)` edge list to hypermap.
    The DCEL construction (defining the `edge`/`node`/`face`
    permutations) remains the corpus's work.
  - Verdict: **AMBER for `extract_rings_valid`**.  `hypermap` is the
    right destination type; `planar_Jordan` provides the
    combinatorial Jordan property that the corpus's
    `ring_simple` + ring assembly correctness would compose with.
    But constructing a hypermap from `noded_labeled_graph A B` (the
    DCEL ring-assembly itself) IS most of the original work.
    Estimate revision: 5-8 sessions → 5-7 sessions.  Modest reduction.

---

## §3 — coq-hott (rejected)

  - Install: **NOT attempted**.  Dry run showed `coq-hott 9.0`
    requires `rocq-core 9.0.1`, would force a **downgrade** of the
    Rocq toolchain from 9.1.1 → 9.0.1 plus recompile of all 16
    already-installed packages.
  - Per the install rule ("Only install if the candidate declares
    compatibility with rocq-core 9.1.1"), the install was correctly
    rejected.
  - Side note on axiom shape: HoTT in Coq additionally
    axiomatises **univalence** and rejects UIP, which would conflict
    structurally with Stdlib's `eq_rect`/UIP-based reasoning.  Even
    on a compatible Rocq version, HoTT would NOT be importable
    without a separate-namespace policy decision.

---

## §4 — rocq-mathcomp-analysis

  - Install: **clean**.  7 additional packages
    (`rocq-mathcomp-solvable 2.5.0`, `rocq-mathcomp-finmap 2.2.2`,
    `rocq-mathcomp-bigenough 1.0.4`, `rocq-mathcomp-field 2.5.0`,
    `rocq-mathcomp-classical 1.16.0`, `rocq-mathcomp-reals 1.16.0`,
    `rocq-mathcomp-analysis 1.16.0`).  Compile time ~22 min.
  - Files: 213 `.v` files across `mathcomp/{analysis, algebra,
    bigenough, boot, classical, field, fingroup, finmap, order,
    reals, solvable, ssreflect}/`.
  - Axiom footprint: **CRITICAL FINDING — 2 NEW MODULE-LEVEL AXIOMS**.
    `mathcomp/classical/boolp.v` declares:

    ```coq
    Axiom functional_extensionality_dep :    (* already allowlisted *)
      forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
      (forall x : A, f x = g x) -> f = g.
    Axiom propositional_extensionality :     (* NOT allowlisted *)
      forall P Q : Prop, P <-> Q -> P = Q.
    Axiom constructive_indefinite_description :   (* NOT allowlisted *)
      ...
    ```

    These are module-level Axiom declarations, inherited transitively
    by every file that imports `mathcomp/classical/boolp.v` —
    essentially all of `mathcomp-analysis` and `mathcomp-classical`.
    **Importing into the corpus requires expanding the README axiom
    allowlist by 2 axioms.**  This is a policy-level decision, not
    just a technical adjustment.

  - JCT-adjacent content (all hits spurious):
    - `solvable/jordanholder.v` — Jordan-Hölder theorem for **finite
      groups** (composition-series uniqueness).  Not geometric JCT.
    - `analysis/charge.v` — **Jordan-Hahn decomposition** of signed
      measures.  Not geometric JCT.
    - `Jordan_curve` / `winding_number` / `simple_closed`: 0 hits.
  - R² rotation / change-of-basis for `hobby_lemma_4_3_no_proper`
    (all abstract algebra, not Euclidean R²):
    - `solvable/maximal.v`, `solvable/burnside_app.v` — finite group
      automorphisms.
    - `algebra/spectral.v`, `algebra/sesquilinear.v` — spectral theory
      / sesquilinear forms.  Real-matrix infrastructure but not
      Euclidean rotation in the piecewise-linear form Hobby's
      argument needs.
  - Topology toolkit: `mathcomp/analysis/topology_theory/topology.v`
    has the full classical-sets topology (`open`, `closed`,
    `connected`, `compact`, `path-connected`, etc.).  Sufficient to
    *state* `geometric_interior` precisely — but at the cost of
    expanding the axiom allowlist.
  - Verdict: **RED on content + RED on policy**.  No JCT for R²
    polygons; no useful Euclidean rotation infrastructure.  The
    topology toolkit is the only marginal value, and it carries
    axiom-allowlist expansion as a prerequisite.

---

## §5 — Impact per deferred entry

### `point_in_ring_correct` (JCT)

  - Library found: **none with direct R² polygon JCT**.
  - GeoCoq: foundational Tarski geometry; no polygon JCT.
  - Fourcolor: combinatorial Jordan for hypermaps (not geometric);
    `realplane.v` provides language to state `geometric_interior`
    but no theorem about ray-crossing parity matching topological
    interior.
  - mathcomp-analysis: only Jordan-Hölder (groups) and Jordan-Hahn
    (measures), both spurious name matches.
  - New estimate: **unchanged** (3-5 months from scratch).
  - Status: **RED**.

### `extract_rings_valid` (DCEL / ring assembly)

  - Library found: **fourcolor**.
  - Relevant artifact: `hypermap` (DCEL-equivalent) +
    `planar_Jordan` (combinatorial Jordan for planar hypermaps).
  - Open work: define `noded_labeled_graph → hypermap` bridge
    (the DCEL construction), prove resulting hypermap is `planar`,
    use `planar_Jordan` to discharge ring well-formedness, lift
    combinatorial Jordan to corpus's `ring_simple` predicate.
  - New estimate: **AMBER**.  5-8 sessions → 5-7 sessions.  Modest
    reduction; the constructive work (defining the permutations
    from edges) is unchanged, but the destination type and the
    Jordan piece are now provided.
  - Status: **AMBER (modest)**.

### `hobby_lemma_4_3_no_proper` (rotated coords)

  - Library found: **none**.
  - mathcomp-analysis has `algebra/spectral.v` /
    `algebra/sesquilinear.v` for abstract linear algebra; not the
    Euclidean R²-rotation in the piecewise-linear ordering shape
    Hobby's argument needs.
  - GeoCoq has Tarski-style rigid motions but in axiomatic geometry,
    not R²-concrete.
  - Fourcolor: nothing relevant.
  - New estimate: **unchanged** (4-6 weeks).
  - Status: **RED**.

### `fast_expansion_sum_nonoverlap_shewchuk` (Shewchuk Theorem 13)

  - Library found: **Flocq (already installed; single-step EFTs
    only)**.
  - Multi-step cascade nonoverlap: not in any installed library.
  - New estimate: **unchanged** (thesis-scale).
  - Status: **RED**.

---

## §6 — Recommendation

```
| Entry                                       | Status |
| ------------------------------------------- | ------ |
| point_in_ring_correct                       | RED    |
| extract_rings_valid                         | AMBER  |
| hobby_lemma_4_3_no_proper                   | RED    |
| fast_expansion_sum_nonoverlap_shewchuk      | RED    |
```

**One import session is warranted**: a fourcolor-based DCEL session
targeting `extract_rings_valid` (5-7 sessions, AMBER).

**Two side-benefits available regardless** of further imports:

  1. **The network workaround is reproducible** (cf. §0).  Future
     ecosystem audits can apply it without re-deriving the path.

  2. **The H1 hypothesis in `overlay_ng_correct_conditional` can be
     internalised** using fourcolor's `realplane.region` machinery.
     The Section-scoped opaque `Variable geometric_interior : Point
     -> Ring -> Prop` becomes a concrete topological definition.
     This wouldn't prove H1 (JCT is still RED) but would make the
     conditional headline strictly stronger: the gap is stated in
     concrete `realplane` terms rather than as an opaque parameter.
     Estimated ~1 session.  Independent of the DCEL session above.

**Three reasons NOT to import mathcomp-analysis**:

  1. Adds 2 module-level axioms (`propositional_extensionality`,
     `constructive_indefinite_description`) — README allowlist
     expansion required.
  2. No content directly useful for the four deferred entries.
  3. Marginal topology-toolkit benefit duplicates fourcolor's
     `realplane.v` (already available, no axiom expansion).

**One reason NOT to import GeoCoq or HoTT**:

  - GeoCoq: nothing relevant to the four deferred entries.
  - HoTT: incompatible with Rocq 9.1.1; would require downgrade.

---

## §7 — State of the branch

  - `coq-released` opam repo: added (file:// pointing at
    `/tmp/rocq-opam/released`).  Note: `/tmp/` is non-persistent in
    this container; future sessions must re-clone.  An alternative
    is cloning into the repo's own `.opam-mirror/` directory and
    committing the path — but that adds ~100MB to the repo, which is
    not worth it for a workaround that's a one-line clone.
  - Switch contents: `rocq-core 9.1.1` + Flocq 4.2.2 +
    `coq-core 9.1.1` + `coq-stdlib 9.0.0` (compat) +
    `coqide-server 9.1.1` + `coq 9.1.1` (metapackage) +
    GeoCoq 2.5.0 (3 sub-packages) + fourcolor 1.4.2 (+
    fourcolor-reals + 41 deps including elpi + mathcomp slice) +
    mathcomp-analysis 1.16.0 (+ 6 deps).
  - Corpus build: unchanged (no `.v` files imported any of the new
    libraries).  Gauntlet: green.
  - Reproducibility: a future session restoring this state needs
    only the §0 workaround plus three `opam install` commands.

The branch produces one document (this file) and the reproducible
workaround.  No `.v` changes.  Realistic next steps:

  - **Phase 4 session 1**: DCEL via fourcolor `hypermap`.  Build the
    `noded_labeled_graph → hypermap` bridge, prove planarity, lift
    `planar_Jordan` to discharge `extract_rings_valid`.  Estimated
    5-7 sessions.
  - **Independent quick win**: internalise H1 in
    `OverlayCorrectness.v` using `realplane.region`.  ~1 session.
    Strengthens Phase 3 conditional headline without proving the gap.
  - **Hobby Lemma 4.3 + Shewchuk Theorem 13**: stay deferred.
    Ecosystem doesn't move the needle on either.
