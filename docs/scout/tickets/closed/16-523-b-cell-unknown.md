<!-- doc-kind: finding
date: 2026-08-30
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# `523-b` — consumers accept `?` as a DE-9IM matrix cell

**Type:** task · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** — · **Spec:** [`spec-523.md`](../../spec-523.md) slice B
**claimId:** `523-b` · **GitHub:** [#604](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/604) · **witness:** `523-b-cell-unknown`

> Umbrella: ticket 523 / #604. Does not retire that issue. Not leftover `Ⅲ`.
> Not a remint of `522-f`.

## Question

`CURVE_RELATE_MATRIX` will emit `?` in cells it did not compute
(`523-c`). Today every consumer rejects that glyph. Teach them `?`
as a **matrix cell** before the driver prints it.

Consumers (`origin/main` @ `5b7a934`):

- `tests/GeosOracleBugHunt/hunt.py` — `RELATE_MATRIX_CHARS = set("F012")`
- `tests/CurveOracleBugHunt/Program.cs` — `ParseRelateWire` same allowlist
- `oracle/relate_matrix.ml` `lookup_matrix` — a 9-char key must be
  `F`/`0`/`1`/`2`
- `oracle/gen_curve_relate_matrix_tests.py` / `curve_relate_matrix_tests.txt`

## Acceptance

**Result parse vs catalog lookup stay split.** A 9-char with `?` is a
valid **result** cell string. It is not a catalog key or a fill key.

1. **Result parse** accepts `?` in a 9-char. A string that contains
   `?` parses as `("matrix", ninechar)`. Example:
   `parse_relate_wire("FF?FF1212")` succeeds as a matrix.
   `is_valid_de9im_result` (or the hunt/C# allowlist) is true for
   that 9-char.
2. Parsers keep two kinds only: `("token", "UNSUPPORTED")` and
   `("matrix", ninechar)`. No third kind for `?`.
3. Whole-line `UNSUPPORTED` stays Decline
   (`RelateNGCore.v : relate_unsupported_no_predicate`).
   `parse_relate_wire("UNSUPPORTED")` is still `("token", …)`.
4. Unknown whole-line tokens still fail
   (`parse_relate_wire("NOT_A_TOKEN")`).
5. Do **not** add `?` to `RELATE_TOKENS`. A bare `?` or a
   whole-line-that-is-not-a-9-char is not Decline.
6. Do **not** steal `UNSUPPORTED` as a cell character.
7. **Catalog lookup** (`lookup_matrix` / fill keys / shared-pin keys)
   still rejects `?`. `catalog_ok_keys` and `shared_pin_ok` stay
   `F/0/1/2`. Do **not** put `?` in catalog keys or in the shared
   classifier pins (FFFFFFFFF / 2FFF1FFF2 / 2FFFFFFF2 / FFFF1FFF2).
   Those pins are also used by `rect_pair_fill`.
8. T-junction decline golden stays `UNSUPPORTED`
   (`oracle/de9im_triangle_vectors.txt` `REGIME DECLINE`). Do not
   turn it into a confident `FFFFFFFFF`. The #530 / #571 pair stays
   classified disjoint (FFFFFFFFF), not a sentinel.

`?` is the issue’s proposed **wire glyph**. It is not a CONTEXT term.
Do not add a glossary entry unless `/domain-modeling` has run and
the owner accepted a name.

This ticket does **not** change `CURVE_RELATE_MATRIX` output. That
is `523-c`, and it waits on this one.

## Non-goals

Do not remint `522-f`. Do not implement leftover `Ⅰ` / `Ⅱ`. Do not
mint `Ⅲ`. Do not emit `?` from the driver here. Do not comment on
GitHub issue 523 unless the user says `comment`.

## Resolution

**Closed 2026-08-30.** Result parse accepts `?` in a 9-char
(`parse_relate_wire("FF?FF1212")` → `("matrix", …)`). Catalog lookup
still rejects `?` (`lookup_matrix "FF?FF1212"` fails). `RELATE_TOKENS`
unchanged. Bare `?` is not Decline. Shared pins and the T-junction
golden stay put. Witness `523-b-cell-unknown`. Same letter claimed
`523-c` after this split. Ticket 523 stays open.
