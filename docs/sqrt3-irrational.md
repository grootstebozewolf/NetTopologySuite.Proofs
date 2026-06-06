# sqrt(3) is irrational — scope and honesty note

This document records what the accompanying Coq development
(`docs/sqrt3-irrational-for-beginners.v`) actually proves and,
more importantly, what it does **not** prove.

## What is proved

- `sqrt 3` is not a ratio of two integers:
  for all integers `p, q` with `q ≠ 0`,

      sqrt 3 ≠ p / q

- The proof is by classical infinite descent on the integers,
  followed by a routine lifting from `Z` to `R` via `IZR`.

- The development is self-contained, uses only the standard
  three classical-reals axioms, and ends with `Qed.` on every
  lemma.

## What is *not* proved (and is not claimed)

This file says **nothing** about:

- Aperiodic tilings of the plane.
- The "einstein" monotile problem (the hat / Spectre family,
  Smith–Myers–Kaplan–Goodman-Strauss 2023).
- Any combinatorial or tiling-theoretic property of hex grids.
- Whether any particular polygon built with `sqrt 3` coordinates
  (see `theories/HatMonotile.v`, the Spectre work, etc.) tiles
  the plane or has any aperiodicity property.

`sqrt 3` appears in the geometry of this project only as the
constant factor `sqrt 3 / 2` that turns integer axial hex
coordinates into the Euclidean plane (the usual "row height"
of a flat-topped or pointy-topped hex grid).  Its irrationality
is irrelevant to the lemmas the corpus actually cares about:

- `ring_closed`, `ring_has_minimum_points`, non-convexity via
  `Orientation.cross`,
- `edge_crosses_ray` / `ray_parity_odd` / `point_in_ring` for
  concrete regression anchors,
- the various bridges in `HexXScaleBridge.v` (which factor the
  scaling out of the *parity decision*, not out of the metric).

All of those lemmas are proved while keeping `sqrt 3` explicitly
present in the expressions and discharging the resulting real
arithmetic with `lra`, `nra`, `field`, or direct sign arguments
on `cross`.  None of them rely on `sqrt 3` being irrational.

## Why include the proof at all?

It is an excellent pedagogical example for people learning Rocq:

- It shows a classic "infinite descent" argument in full detail.
- It illustrates the (sometimes fiddly) passage between `Z` and `R`.
- It demonstrates how to turn a "there is no positive solution"
  statement into a "the only integer solution is zero" statement
  via a measure (here `Z.to_nat (Z.abs a)`).
- It is a nice follow-on exercise after
  `docs/pythagoras-for-beginners.v`.

The file is therefore deliberately placed under `docs/` as a
teaching tool, exactly like the Pythagoras beginner file, and
is not part of the main proof corpus under `theories/`.

## Relation to the rest of the project

If you came here because you are looking at `HatMonotile.v`,
`SpectreCurvedEdge.v`, `HexXScaleBridge.v`, or the various
hex-lattice regression anchors, you can safely ignore this file
for the geometric content.  The project already documents the
same honesty position in the headers of those files.

The irrationality of `sqrt 3` is a lovely fact.  It just isn't
one of the facts this particular formalisation effort needs.
