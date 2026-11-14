<!-- doc-kind: finding
date: 2026-08-22
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Retire #65 — buffer and offset curves

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** — · **Closed:** 2026-08-22

## Question

#65 (Urgent) asks for parallel-curve correctness, joins, endcaps, topology,
`CurvePolygon` emission and oracle modes. The audit reads **MOSTLY**: eight of ten
asks satisfied, and the body's round-2 item 1 has landed since. Does it close, and
where does its residue go?

Satisfied (verify then cite): with-holes extraction now reduces to the *same*
single `face_twin_free` residual as the hole-free case
(`theories/ExtractHolesWellNoded.v`), and that residual is itself Qed via
`theories/FaceOrbitSep.v:154 face_twin_free_of_sep` — the chain is called
"discharged end-to-end" in `docs/face-twin-free-closure-plan.md` §1. Miter and
flat-cap assembly wired (`BufferAssembly.v : assemble_open_miter_chain`,
`BufferEndcap.v : flat_cap_ring_closed`). Curve ladder rungs 1–14, P1, P3,
`CurveBufferArea.v` green; the clothoid chain gives a simple-closed-curve
certificate under clearance > 2·|d|. Oracles `BUFFER_REGION`, `ARC_OFFSET_XY`,
`ARC_BUFFER_SIMPLE`, `ARC_OFFSET_FILTERED` all present. Honest negatives intact
(`BufferDepth*Counterexample.v`, `inner_offset_past_center_not_at_distance`,
`tangent_continuity_insufficient_for_offset`).

Residue to place:

1. Per-hypothesis disposition of `BufferCorrectness.v : buffer_correct_conditional`'s
   two named hypotheses (`H_valid`, `H_bridge`, lines 106-150) against the
   guard-only spine.
2. Round-join **assembly**: `CurveRoundJoin.v` proves `round_join_arc_valid` and
   `_connects`, but nothing wires them into `BufferAssembly`; plus the multi-edge
   two-sided open-chain walk.
3. Self-intersecting offset cleanup for non-convex inputs.
4. P2 Minkowski point-set semantics — **parked by decision**. Decide whether it
   becomes a documented non-goal rather than an issue, since filing it would
   re-open something deliberately closed.

## Resolution

**Closed 2026-08-22. #65 closed on linear + circular-arc scope; the hero shot is
#515. Three of the four residue items in this ticket were stale, and verifying
turned up a live soundness bug.**

**The framing that decided it**: buffer with curve preservation is the showcase
deliverable, and the sequencing is zoo first, then buffer over it. Today's whole
curve-offset ladder assumes circular arcs, so the hero shot is necessarily
downstream of #508 — which makes #65 its arc-only predecessor, not the epic
itself.

**What this ticket got wrong, corrected by verification:**

| Ticket said | Actually |
|---|---|
| `H_valid` and `H_bridge` both need disposition | **`H_valid` is discharged** — unconditionally hole-free (`ExtractBufferRings.v:115/:132`, Euler-free), with-holes down to one `hole_inside_outer`. `H_bridge` is **split** (`BufferBridge.v:101/:123`) with soundness supplied (`BufferBridgeSound.v:163/:174`); only **completeness** remains. |
| Round-join assembly + multi-edge two-sided walk are follow-ups | **Struck.** The walk landed 2026-07-05 (`BufferAssembly.v:541/:554`, Qed). Round-join-into-`BufferAssembly` is a documented **type mismatch** (an arc does not fit that file's `list (Point*Point)` model, `:39-42`), already served on the curve side and in the oracle — not a gap. |
| P2 is "parked by decision" | **No such decision exists.** The only "parked by decision" phrasing was *this ticket asking the question*. The corpus says *"sequence P2 after P5"* (`audit-rgr-comparison.md:656`) and excludes P2 from the parked set (P11–13). Recorded as **ADR-0002**. |
| Self-intersecting offset cleanup | Confirmed absent, and it is **engineering not proof** — thread `BufferDepth` labelling through `build_labeled_graph`, since `result_edges op (build_graph segs) = []` for every `BooleanOp`. → #515 item 3. |

**On the maintainer's challenge to "research-scale"** — it did not survive. The
point-set semantics is already formalised (`BufferCorrectness.v:57 buffer_spec`
with two Qed sanity theorems), proven Minkowski machinery exists
(`PenetrationMinimax.v:78`), a dense-Minkowski differential pin exists, and the
corpus's own rating is "medium–high, multi-session, sequence AFTER P5". A
research park here means *no published true statement* — the bar the arc-Hobby
analog meets and P2 does not. Better still, `even_parity_escapes` is Qed for
rectangles and triangles (`JCTSeparation.v:113/:141/:156`), so a **witness-scoped**
bridge over demo shapes is available now with no new machinery. ADR-0002 also
pins the vocabulary so the conflation cannot recur, and CONTEXT.md now defines
*sequencing park*, *research park* and *witness-scoped*.

**Found while verifying, both filed:**

- **#513** — `BUFFER_REGION` emits a plausible `AREA` where its own header
  promises `DEGENERATE`: the guard at `driver.ml:3042-3055` has an **empty
  `else`**, so a gapped ring gets shoelaced. This mode is `CurveBufferArea.v`'s
  named oracle, making it a wrong *reference*. The cleanup its comment blames is
  unreachable dead code whose intersection algebra looks wrong, so re-enabling it
  is not a safe fix.
- **#514** — three advertised capabilities that reduce to a one-sided stub
  printing `AREA 0`, a string prefix (`ARC_OFFSET_FILTERED` is `ARC_OFFSET_XY`
  verbatim), and that dead code.

**The Coq lane is clean** on the same failure mode: every linearisation is named
in the identifier, and `CurveBufferArea.v` computes the true circular-segment
area of the *offset* arc, not a chord area. Two documentation overclaims were
noted in passing — `ExtractHolesWellNoded.v:14` says "the SAME single gap" while
carrying two further oracle clauses, and `face-twin-free-closure-plan.md:16`'s
"discharged end-to-end" sits under a heading reading "closed **(conditionally)**"
with H5/H6 still open.
