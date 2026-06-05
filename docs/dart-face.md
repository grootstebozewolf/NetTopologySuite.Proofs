# Face step + face orbit finiteness — `extract_rings_valid` R5, slice 2f

**Coq artifact:** [`theories/DartFace.v`](../theories/DartFace.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals pair).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md)
§5 step 2, converging the whole `next` programme:
[`docs/orbit-cycle.md`](orbit-cycle.md) (2e),
[`docs/dart-next-injective.md`](dart-next-injective.md) (2d).

---

## Why this slice

This is where the whole `next` programme converges. The §9 crux is
**`face_orbit_finite`**: iterating the face step from a dart returns to it, so a
face boundary is a finite closed walk. Slice 2e proved the abstract kernel
(injective self-map of a finite set cycles back); this slice builds the concrete
dart face step and discharges that kernel's hypotheses.

## The face step

```coq
Definition fstep (D : list Dart) (d : Dart) : Dart :=
  next (outgoing (dtip d) D) (twin d).
```

Cross the edge to the head vertex (`twin`), then turn to the rotationally
adjacent outgoing dart there (`next`). The orbit of `fstep` is a face boundary.

## The well-formed arrangement

```coq
Definition arrangement_ok (D : list Dart) : Prop :=
  (forall d, In d D -> In (twin d) D)            (* twin-closed *)
  /\ (forall v, fan_ok (outgoing v D)).          (* every vertex fan well-formed *)
```

`arrangement_ok_darts_of` shows the twin-closure is **free** for a `darts_of E`
dart set (`darts_of_closed_under_twin`), so a caller need only supply the
per-vertex `fan_ok` (the noded-arrangement general-position guarantee).

## What's proved

| lemma | content |
|---|---|
| `fstep_in` | `fstep` keeps darts in `D` — orbit closure (`next_in` + `outgoing ⊆ D` + twin-closure) |
| `fstep_inj` | `fstep` is injective on `D` |
| **`face_orbit_finite`** | `∃ n ≥ 1, iter (fstep D) n d = d` — the face walk returns |
| `face_walk_in` | every face-walk dart stays in `D` (finiteness of the visited set) |

`fstep_inj` is the crisp part: equal images `fstep d1 = fstep d2` are based at
`dtip d1` and `dtip d2` respectively (`next_base`), so they share a head vertex
`v`; then both steps run `next` on the *same* fan `outgoing v D`, where slice
2d's `next_injective` gives `twin d1 = twin d2`, hence `d1 = d2` (`twin_inj`).

`face_orbit_finite` is then a **direct instantiation** of slice 2e's
`orbit_returns` with `f := fstep D`, `S := D`, discharging `Hclos`/`Hinj` by
`fstep_in`/`fstep_inj`.

## Deliberately deferred (the assembly)

- **`face_of` as a ring** — read the closed `fstep`-orbit off as an ordered
  vertex list, a `closed_chain` / `ring_closed` ring, feeding
  `RingExtract.ring_of_chain`; with `face_walk_in` bounding its length this also
  gives `ring_has_minimum_points` for a non-degenerate face.
- **hole nesting** — the face-incidence tree, ⇒ the combinatorial core of
  `valid_polygon`; then the named analytic `hole_inside_outer` residual (§4).

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
