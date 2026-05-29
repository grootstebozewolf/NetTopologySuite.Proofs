# Rocq ecosystem search — 2026-05-29

**Scope.**  Audit the installed Rocq/opam environment for libraries that
could close or substantially reduce the four major deferred entries
in the corpus before Phase 4 starts.

**Outcome.**  All four deferred entries remain **RED** (nothing
relevant found).  Outcome consistent with the earlier S8 JCT-search
finding (`docs/audit-phase3-milestone5.md` §4.2): the corpus's opam
switch is configured with `opam.ocaml.org` only; the Coq community
repository (`coq.inria.fr/opam/released`) where mathcomp / GeoCoq /
fourcolor / HoTT / Coquelicot / Interval live is **not reachable**
under the current network policy.  This is an environmental
limitation, not a finding about the libraries' contents themselves.

---

## §1 — Search results by library

### Part A: GeoCoq

  - Installed: **no**.
  - `opam search geocoq`: no matches.
  - Filesystem scan: no `.v` files.
  - Impact: **none available**.

### Part B: mathcomp-analysis (topology, classical sets, separation)

  - Installed: **no** (neither `mathcomp-analysis`,
    `mathcomp-classical`, `mathcomp-topology`).
  - `opam search mathcomp`: no matches.
  - Filesystem scan: no `.v` files outside Stdlib's own ssreflect.
  - Impact: **none available**.

### Part C: mathcomp fingraph / fourcolor

  - Installed: **no** (`mathcomp`, `fingraph`, `fourcolor`).
  - `opam search fourcolor` / `mathcomp`: no matches.
  - Filesystem scan: nothing matching `planar` /
    `face_traversal` / `DCEL` / `half_edge` / `HalfEdge`.
  - Impact: **none available**.

### Part D: Coq-HoTT / topology

  - Installed: **no** (no HoTT, no `coq-topology`).
  - `opam search hott` / `topology`: only ocaml process-snapshotting
    libraries (false-positive name matches).
  - Filesystem scan: no `Jordan_curve` / `winding_number` /
    `simple_closed` / `path_connected` anywhere.
  - Impact: **none available**.

### Part E: Flocq expansion arithmetic (Shewchuk gap)

  - Installed: **yes** (Flocq 4.2.2, in
    `~/.opam/nts-flocq/lib/coq/user-contrib/Flocq/`, 35 `.v` files).
  - Single-step EFTs **already present**:
    - `Flocq/Pff/Pff.v`: `Dekker`, `DekkerN`, `DekkerS1`,
      `DekkerS2`, `Dekker1`, `Dekker2`, `Dekker_FTS`,
      `TwoSumProp` (Pff layer).
    - `Flocq/Pff/Pff2Flocq.v`: `TwoSum_correct`, `Dekker`
      (Flocq-lifted versions).
    - `Flocq/Prop/Sterbenz.v`: `sterbenz`.
    - `Flocq/Prop/Mult_error.v`: `mult_error_FLT`.
  - These are the SINGLE-STEP primitives the corpus already consumes
    via `theories-flocq/B64_Pff_bridge.v`'s `b64_TwoSum_correct` and
    `b64_Fast2Sum_correct`.
  - **Multi-step cascade results (fast_expansion_sum, grow_expansion,
    nonoverlap preservation, Shewchuk Theorem 13)**: NOT in Flocq.
    Grep on `expansion` / `nonoverlap` / `cascade` /
    `grow_expansion` / `fast_sum` returns 0 hits across all 35
    Flocq files.
  - Impact: **already maximally leveraged**; the cascade-level
    Shewchuk result has no upstream provider in any installed library.

### Part F: mathcomp linear algebra (rotation / change-of-basis)

  - Installed: **no** (no `mathcomp-algebra`, no `mathcomp-fingroup`,
    no `Coquelicot`).
  - Filesystem scan: nothing matching `rotation_matrix` /
    `rotation_mx` / `change_of_basis` / `linear_map` / `isometry`
    anywhere under `/root`.
  - Stdlib `theories/Reals/`: no `rotation` / `isometry` /
    `orthogonal_matrix`.
  - Impact: **none available**.

### Part G: Available-but-unchecked opam packages

The default `opam.ocaml.org` repository's full `coq` /
`rocq`-related package list:

  - Installed: `rocq-core 9.1.1`, `rocq-runtime 9.1.1`,
    `rocq-stdlib 9.0.0`.
  - Available (not installed): `coq-lsp`, `coq-serapi`,
    `coq-of-ocaml`, `coq-waterproof`, `coqide`, `coqide-server`,
    `farith`, `hol2dk`, `lambdapi`, `lem`, `orthologic-coq`,
    `coq` (metapackage), `coq-stdlib` (metapackage),
    `vscoq-language-server`, `coq-shell`, `coq-native`,
    `coq-catt-plugin`, `binary_tree` (false-positive name),
    `rocq-prover`, `rocqide`, `vsrocq-language-server`,
    `rocq-devtools`, `rocq-native`.
  - **None of these contain geometry / topology / planar-graph /
    Jordan-curve / DCEL / expansion-arithmetic content.**  The list is
    tooling (IDEs, language servers, plugins) and translators
    (`hol2dk`, `lambdapi`, `coq-of-ocaml`).

The actual Coq math libraries (GeoCoq, mathcomp, fourcolor, HoTT,
mathcomp-analysis, Coquelicot, Interval) are distributed via the
**Coq community opam repository**
(`https://coq.inria.fr/opam/released`), which the corpus's switch
does NOT have configured:

```
$ opam repo list
 1 default https://opam.ocaml.org
```

---

## §2 — Impact assessment per deferred entry

### `point_in_ring_correct` (JCT)

  - Library found: **none**.
  - Relevant theorem: none.
  - New estimate: **unchanged** (3-5 months from scratch, per audit
    doc §4.2).
  - Recommendation: **still out of budget**.  The audit doc's S8
    decision (Path B: register the gap, state the conditional
    headline) stands.  When the network policy permits adding the
    Coq community repo, re-run this audit specifically for GeoCoq
    and mathcomp-analysis.

### `extract_rings_valid` (DCEL / ring assembly)

  - Library found: **none**.
  - Relevant theorem: none.
  - New estimate: **unchanged** (3-8 sessions per audit doc §4.3,
    requires DCEL adoption).
  - Recommendation: **build from scratch**.  Fourcolor (the most
    promising upstream candidate per audit doc §4.3) is in the Coq
    community repo and unreachable.  The audit doc's recommendation
    to adopt DCEL via a Session-1.5 M4-revision remains the only
    realistic path inside the current environment.

### `hobby_lemma_4_3_no_proper` (rotated coordinates / piecewise-linear ordering)

  - Library found: **none**.
  - Relevant theorem: none.
  - New estimate: **unchanged** (4-6 weeks per
    `docs/admitted-deferred-proofs.txt`).
  - Recommendation: **still deferred**.  The rotated-coordinate
    change-of-basis would benefit from `mathcomp-algebra` (rotation
    matrices, orthogonal groups) which is not installed and not
    available via the default opam repo.  Hobby's Lemma 4.3 remains
    a thesis-shaped piece; the linear-algebra infrastructure would
    reduce the formalisation burden but doesn't change the
    mathematical content.

### `fast_expansion_sum_nonoverlap_shewchuk` (Shewchuk Theorem 13, general)

  - Library found: **Flocq (already installed, already consumed)**.
  - Relevant theorems: `Dekker`, `TwoSum_correct` — SINGLE-step EFTs
    only.  The corpus already lifts these via `B64_Pff_bridge.v`.
  - Multi-step cascade nonoverlap: **not provided by any installed
    library**.
  - New estimate: **unchanged** (thesis-scale per the 2026-05-29
    re-classification in `docs/admitted-deferred-proofs.txt`).
  - Recommendation: **still thesis-scale**.  The Boldo / Boldo-
    Melquiond / BJMP papers (ITP 2017 §4 in particular) are the
    upstream sources but have not been published as a Coq library;
    the cascade-level Shewchuk Theorem 13 has no upstream Coq
    provider anywhere I can verify.

---

## §3 — Recommendation per deferred entry

| Entry                                       | Status |
| ------------------------------------------- | ------ |
| `point_in_ring_correct`                     | **RED** |
| `extract_rings_valid`                       | **RED** |
| `hobby_lemma_4_3_no_proper`                 | **RED** |
| `fast_expansion_sum_nonoverlap_shewchuk`    | **RED** |

All four deferred entries remain RED.  No import session is warranted
based on what is reachable in the current environment.

The root cause is environmental, not substantive: the **Coq
community opam repository is not configured for the corpus's switch**.
This was already identified during S8 (audit doc §4.2).  When the
network policy permits adding it, the priorities for re-audit are:

  1. **GeoCoq** — most likely to contain JCT-adjacent results for
     polygons.  Targets `point_in_ring_correct` (BLOCKING for Phase 3
     unconditional landing).
  2. **mathcomp + fourcolor** — most likely to contain DCEL /
     planar-graph face-traversal machinery.  Targets
     `extract_rings_valid` (BLOCKING for Phase 3 unconditional
     landing).
  3. **mathcomp-algebra** — rotation matrices + orthogonal groups.
     Targets `hobby_lemma_4_3_no_proper` (reduces formalisation
     burden but doesn't eliminate the mathematical work).
  4. **mathcomp-analysis** — topology / classical sets / separation.
     Targets the JCT gap if GeoCoq doesn't provide it.

Until the repo configuration changes, the Phase 2 / Phase 3
conditional landings (`hobby_theorem_4_1_conditional`,
`overlay_ng_correct_conditional`) stand as the best realistic
ground.  Both are Qed-closed with named gaps; the gaps are not
discharge-able within the present environment.

---

## §4 — Libraries worth installing (if repo policy changes)

If the Coq community repo (`coq.inria.fr/opam/released`) becomes
reachable, install these in order of expected payoff per session
of import work:

  1. `coq-geocoq` — JCT-adjacent separation theorems for plane
     geometry.  Estimated payoff: HIGH for `point_in_ring_correct`.

     ```sh
     opam repo add coq-released https://coq.inria.fr/opam/released
     opam install coq-geocoq
     ```

  2. `coq-fourcolor` — planar graph face-traversal + Jordan-curve
     consequences for planar graphs.  Estimated payoff: HIGH for
     `extract_rings_valid` (provides face structure the corpus
     would otherwise have to build from scratch).

     ```sh
     opam install coq-fourcolor
     ```

  3. `coq-mathcomp-analysis` (pulls `coq-mathcomp-{classical,
     ssreflect, algebra, fingroup, ...}`) — topology, classical
     sets, normed spaces, rotation matrices via the algebra
     dependency.  Estimated payoff: MEDIUM for all three remaining
     entries (touches JCT, rotated coordinates, and provides the
     linear-algebra infrastructure for Hobby Lemma 4.3).

     ```sh
     opam install coq-mathcomp-analysis
     ```

  4. `coq-coquelicot` — real analysis (less directly relevant but
     fills standard analytical gaps that the Stdlib's `Reals` is
     known to lack).  Estimated payoff: LOW (no specific deferred
     entry directly benefits).

     ```sh
     opam install coq-coquelicot
     ```

Note: the version pinning (Rocq 9.1.1 + Flocq 4.2.2) may constrain
which versions of these libraries are compatible.  A future audit
should check Rocq-9-compat tags before assuming installability.

---

## §5 — Methodology note

All searches were run on the corpus's container at 2026-05-29.  Each
search was a combination of:

  - `opam list 2>/dev/null | grep -i <name>` (installed package
    check).
  - `opam search <name>` (available-package check against configured
    repos).
  - `find /root -name "*.v" 2>/dev/null | xargs grep -l <pattern>`
    (filesystem-wide content scan).

The filesystem scan is the strongest negative result: even libraries
NOT registered with opam but present on disk (e.g. user-contrib
drops) would surface.  Nothing did, beyond the 35 Flocq `.v` files
already enumerated.

The opam repo configuration is the single environmental factor that
gates the rest: the default `opam.ocaml.org` does not carry the Coq
community library set.  The audit doc §4.2 from May 2026 documented
this; this audit re-confirmed it 14 days later.
