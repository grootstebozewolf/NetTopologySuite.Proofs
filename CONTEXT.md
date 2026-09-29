# NetTopologySuite.Proofs

A Rocq/Coq proof corpus accompanying NetTopologySuite, plus the differential
tooling that compares real geometry engines (NTS, GEOS) against the extracted
oracle and pictures the cases under scrutiny.

## Language

### Arrangement vocabulary

Per **ADR-0007**. Each term names one thing precisely; the short name is the
one to use in issue titles and lemma names, the gloss is what it means. None
ADR-0007 is *Accepted* (Joost, BDFL, 2026-09-07).  Four of the seven now
exist as types in `theories/SheetHenCook.v`: `Sheet` (Record), `Hen`
(Definition), `Egg` (Inductive), `Chicken` (Record).  `Cook` and `View` are
not types; `Decline` is a constructor, `IDecline` of `IResult`, not a type.

**Sheet**:
An oriented affine plane `(O; e1, e2)` with an optional lattice (the snap
grid). All coordinates are points of one sheet, and a constructor runs on
exactly one. Changing the sheet or the lattice is a different instance. This
is the envelope JTS leaves unnamed when it stores a bare `Coordinate` and
later attaches a scale.
_Avoid_: precision model, coordinate system (both name only part of it)

**Hen**:
A stable identifier with decidable equality. A hen owning a point is a
vertex; a hen owning an egg is a curve piece. Identity of vertices is a
property of the hen, **not** of its coordinates -- which is the whole point:
`Dart := (Point * Point)` makes two coincident crossings rounded to different
floats into two darts that `dart_eq_dec` correctly reports as distinct.
_Avoid_: vertex, node, id (each is a role a hen plays, not the thing)

**Egg**:
The interpolant `gamma : [0,1] -> sheet` of a named class (chord, circular
arc, clothoid, sinusoid, ellipse, Bezier, NURBS), supporting `eval`,
`tangent`, curvature where defined, `split` and `demote`.
_Avoid_: curve, segment (both are classes of egg, not the concept)

**Chicken**:
Incidence, and only incidence: a directed use `(h_src, h_dst, egg)` of an egg
between two hens. Its twin reverses orientation. A hen incident to no chicken
is **vacant**.
_Avoid_: edge, half-edge, dart (dart is the corpus's current, coordinate-
carrying approximation of a chicken)

**Cook**:
A constructor: a partial function that allocates hens. The primitive is the
pairwise intersection oracle, which returns a point plus its two parameters,
or the empty set, or **declines**. The cook is the only way a new hen appears.
Priest 1991 §7 is a cook for a line and a segment in floating point.
_Avoid_: noder, intersector (these name implementations of one cook)

**Decline**:
The oracle was undefined for this pair, or the inputs are not on one sheet.
**Not** an empty geometry, not `EMPTY`, not a value in SQL/MM. Distinguish
sharply from a completed cook that left no hens, which *is* the empty
point-set (dimension -1, union identity, intersection zero).
_Avoid_: empty, null, failure (the first is a different result, the others
lose the distinction)

**View**:
A function from leftover hens to a wire format -- WKT, WKB, SFA class names,
SQL/MM type tags. `POINT EMPTY` is a tag a view chooses for a vacant result
whose caller expected a point; the kernel does not store it. The SFA type
zoo lives here, not in the kernel.
_Avoid_: geometry type, output format
