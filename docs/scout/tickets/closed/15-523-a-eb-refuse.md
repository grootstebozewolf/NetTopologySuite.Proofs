<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# `523-a` — `CURVE_RELATE_MATRIX` refuses elliptic / Bézier

**Type:** task · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** — · **Spec:** [`spec-523.md`](../../spec-523.md) slice A
**claimId:** `523-a` · **GitHub:** [#603](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/603) · **witness:** `523-a-eb-refuse`

> Umbrella: ticket 523 / #603. Does not retire that issue. Not leftover `Ⅲ`.
> Not a `522-*` letter.

## Question

Elliptic / Bézier pairs in `CURVE_RELATE_MATRIX` return `[]` or a
centre / control-chord proxy and print `"FFFFFFFFF"`. Refuse them
instead, the way the buffer modes already `failwith` on `E` / `B`.

Grill cites (`origin/main` @ `5b7a934`; re-cite if they drift):

- Lineal `pair_pts` → `[]` → `"FFFFFFFFF"` (`oracle/driver.ml:3983–3985`,
  `:4080`, `:4090`)
- Areal centre / control-chord proxy (`:4195–4204`, `:4236–4238`,
  `:4303–4308`)
- Buffer precedent: `BUFFER_REGION:3353`, `BUFFER_UNIFIED:3482`,
  `ARC_BUFFER_SIMPLE:3372`

## Acceptance

1. Any `E` / `B` segment in either argument refuses the mode.
   Shape: `failwith`, same as those three buffer modes.
2. The mode does **not** print a 9-char. It does **not** print
   `"FFFFFFFFF"`. It does **not** print `UNSUPPORTED` — that is a
   relate Decline (`RelateNGCore.v : relate_unsupported_no_predicate`),
   not a capability refuse.
3. Do **not** use `LENGTH_UNIFIED` as the precedent (it accepts E/B
   and computes).
4. Year 1 stays circular. Do not add Exact\* zoo carriers. Do not
   extend `CurveSegment`. Do not start 64-a r·θ. Refuse until #508.

No consumer-token gate. This ticket can land before `523-b` / `523-c`.

## Non-goals

Shared pins stay put (FFFFFFFFF / 2FFF1FFF2 / 2FFFFFFF2 / FFFF1FFF2).
Decline golden stays `UNSUPPORTED`. Do not implement `523-b` / `523-c`
here unless the same letter claims them. Do not mint `Ⅲ`. Do not
comment on GitHub issue 523 unless the user says `comment`.

## Resolution

**Closed 2026-08-30.** `run_curve_relate_matrix` `failwith`s when either
argument has an `E` / `B` segment. No 9-char, not `UNSUPPORTED`. Same
shape as `BUFFER_REGION` / `BUFFER_UNIFIED` / `ARC_BUFFER_SIMPLE`.
Witness `523-a-eb-refuse`. Same letter also claimed `523-b` / `523-c`.
Ticket 523 stays open.
