# ATTACK hobby-hlemma43-uninhabitable
- claimId: none
- file:lemma: theories-flocq/HobbyTheorem_b64.v:hobby_theorem_4_1_conditional
- class: uninhabitable
- epic: #66
- topic: overlay
- verdict: QEX-uninhabitable
- H1-shaped: yes

Target behaviour: snap-rounding of a `fully_intersected` arrangement stays
`fully_intersected` (Hobby 1999, Theorem 4.1).

Attacked binder: the **anonymous second premise** of
`HobbyTheorem_b64.v : hobby_theorem_4_1_conditional` (the `forall s1 s2,
segments_intersect_only_at_endpoints s1 s2 -> …` arrow). Prose alias
Hlemma43 lives in `docs/hobby-lemma-4-3-no-proper-refutation.md`; it is
not a `Hypothesis` ident in the `.v`.

## Repro

```sh
# After a Flocq-lane build that produces HobbyCounterexample_b64.vo:
bash scripts/hunt_probe_smoke.sh
# or:
rocq c -Q theories NTS.Proofs -Q theories-flocq NTS.Proofs.Flocq \
  docs/h1-vacuity/HobbyHlemma43Check.v
```

Grep the second arrow against the aborted lemma and the only-at-endpoints
disjunct:

```sh
rg -n -A8 'Definition segments_intersect_only_at_endpoints' theories-flocq/HobbyTheorem_b64.v
rg -n -A20 'Theorem hobby_theorem_4_1_conditional' theories-flocq/HobbyTheorem_b64.v
rg -n 'hobby_lemma_4_3_no_proper_is_false|originals_no_proper|snapped_proper' \
  theories-flocq/HobbyCounterexample_b64.v
```

Probe theorems (both must end `Qed.` on the flocq smoke):

- `collapse_pair_only_at_endpoints` — the collapse pair inhabits the
  second premise's antecedent
- `Hlemma43_uninhabitable` — the reconstructed second premise derives
  `False`

## What collapses

`hobby_theorem_4_1_conditional` is

```
fully_intersected A ->
  (forall s1 s2, only_at_endpoints s1 s2 -> snapped singletons stay only_at_endpoints) ->
  fully_intersected (snap_round_segments A).
```

`segments_intersect_only_at_endpoints` is `~ proper \/ share_endpoint`
(HobbyTheorem_b64.v). The comment says "or not at all." Parallel segments
`A = (0, 0.7)–(10, 0.7)` and `B = (3, 1.3)–(7, 1.3)` share no point, so
`~ proper` holds, so the antecedent is inhabited
(`HobbyCounterexample_b64.originals_no_proper`). Their unit-grid snaps
overlap properly at `(5, 1)` and share no endpoint
(`snapped_proper`). Therefore the second premise is the same false
universal as the `Abort`ed `hobby_lemma_4_3`. Nobody can discharge it.
The headline Qeds as `fully_intersected A -> False -> …` — the overlay
H1 shape.

The file header and `docs/hobby-lemma-4-3-no-proper-refutation.md` still
call the headline "unaffected" because it "merely assumes" that arrow.
Assuming a false premise is how `overlay_ng_correct_conditional` became
uninstantiable.

## Consumer chain

no live apply of `hobby_theorem_4_1_conditional`.
`theories-flocq/OverlayBridge.v:snap_noding_bridge` comments the
headline as the noding discharge, then forgets every hyp
(`intros A B _ _ _; apply valid_topology_graph_build_graph`).
`theories-flocq/NodingSeparation_b64.v` applys only the true half
`hobby_lemma_4_3_shared_endpoint`. The false halves
`hobby_lemma_4_3_no_proper` and `hobby_lemma_4_3` are `Abort`, so they
are not apply-poison.

Print Assumptions captured from flocq smoke on `3515626` (run
`33720186385`, job “Smoke hunt probes”).

`Hlemma43_uninhabitable` (first block):

```
ClassicalDedekindReals.sig_not_dec
ClassicalDedekindReals.sig_forall_dec
FunctionalExtensionality.functional_extensionality_dep
Classical_Prop.classic
```

`collapse_pair_only_at_endpoints` (second block):

```
ClassicalDedekindReals.sig_forall_dec
FunctionalExtensionality.functional_extensionality_dep
```

`classic` is the snap-layer lineage. The probe is listed in
`docs/audit-exceptions.txt` and the flocq smoke log (prefixed
`ROCQ compile`) is concatenated into the axiom-audit input. No extra
axiom beyond that lineage.

## Not a fix

Do not add a new named hyp `H_noded` / `H_arrangement` so the same
false universal still Qeds. That re-creates H1. The inhabit-able
replacement already exists: `NodingSeparation_b64.fully_intersected_snap_of_nodable`
under `pairwise_nodable` (share an endpoint or axis-separated by more
than one grid unit). Re-point the headline onto that predicate; do not
wrap the second premise.

## Promote?

`HobbyTheorem_b64.v : hobby_theorem_4_1_conditional` is
QEX-uninhabitable, not an honest `[cond]`. The second premise is the
aborted `hobby_lemma_4_3` under a new binder. Probe:
`docs/h1-vacuity/HobbyHlemma43Check.v`. Honest discharge already lives
at `fully_intersected_snap_of_nodable`. Tracker #66 stands completed
(2026-08-22); this ticket is a status-table correction, not a reopen.
Do not wrap the false hyp. Joost/Jeroen: promote or stand down.

OUTCOME: LANDED (flocq smoke on `3515626` compiled the probe; both
theorems Qed; PA logged above).
