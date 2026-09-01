# SQL/MM WKT oracle — CLOTHOID / CIRCLE / GEODESICSTRING / NURBSCURVE / SPIRALCURVE

**Type:** implement · **Map:** [COMPOUNDCURVE](../../map-compoundcurve.md) (packet-wide I/O)
**Claimed:** implement 2026-09-01 · **Closed:** 2026-09-01
**Blocked by:** tickets 30 / 32 / 34 / 36 (type honesty named on GEOS)
**claimId:** none · **GitHub:** none · **witness:** none

## Ask

Implement the structural oracle for the §4.2.1 instantiable ST_Curve
subtypes that the engines do not yet carry, and for optional
extensions such as the documented deviations from the standard.

A `SPIRALTYPE` value may contain anything but a comma or a
parenthesis. The standard defines `<spiraltype text>` as free-form
`<letters>`, and §5.1.68 length-prefixes the value in WKB, so the
value set is open — §4.2.12 lists `clothoid`, `bloss`,
`biquadratic`, `sine` and `cosine` only as the *initial* set. Text
has no length prefix, and `<letters>` admits the characters that
would end the value, so the lexer reads a spiral type up to the
comma or closing parenthesis that terminates it. Interior spaces
are preserved, so `SPIRALTYPE Wiener Bogen` parses. A name
containing a comma or a parenthesis is the one case this grammar
cannot represent.

Cite ISO/IEC 13249-3. No DOI. No 19125-2.

## In scope

- Oracle mode `SQLMM_WKT` (structural parse / refuse / type identity).
- SPIRALTYPE open-set lexer deviation, pinned by red tests.
- Documented deviations: keyword case-fold, tagged LINESTRING in
  COMPOUNDCURVE.
- ELLIPTICALCURVE as instantiable §4.2.9 (not UNKNOWN).

## Out of scope

- GEOS / NTS / JTS carriers. `CurveSegment` growth. `508-*` remint.
- Leftover `Ⅺ`. Length mint of `K` / `N` tokens (M-LEN-ZOO stays).
- Type-9/10/11/12 reader PRs. JTS #7 CLOTHOID-in-COMPOUNDCURVE
  3-arg proposal. Koc railway compound.
- Inventing WKB codes (Table 15 lists 8–12 only).

## Resolution

**Implemented 2026-09-01** on Proofs (`cursor/sqlmm-type-honesty-ccfa`).

Named site: `oracle/sqlmm_wkt.ml` + driver mode `SQLMM_WKT`.
Red tests: `oracle/red_sqlmm_wkt_tests.py`. Clause-book §4.1 / §8
record the productions and the SPIRALTYPE lexer deviation.

No new Coq lemma. claimId: none. witness: none.
Do not remint `508-*`. Do not grow `CurveSegment`.
