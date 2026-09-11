# Grammar pin — antlr/grammars-v4 PR #4997

Source of truth for ISO/IEC 13249-3 §5.1.67 WKT syntax.

| Field | Value |
|---|---|
| Upstream | https://github.com/antlr/grammars-v4/pull/4997 |
| Title | `[wkt] ISO/IEC 13249-3 5.1.67: add 8 geometry types, complete 3 more` |
| Status | **MERGED** 2026-09-08 |
| Merge commit | `181f4c92657a107f1fb64412738de5aa5143ea05` |
| Files | `wkt/wktLexer.g4`, `wkt/wktParser.g4` |
| Clothoid fixture | `wkt/examples/example5.txt` (both CLOTHOID forms; one COMPOUNDCURVE carries both) |

Copies under `grammar/` are byte-pinned at that commit. Do not invent
productions. Do not treat `example3.txt` as an oracle source.

OGC forms still parse (PR body). ISO form of CLOTHOID is told apart
from the JTS `(k0, k1, L)` form by the token after the opening
parenthesis (`REFERENCELOCATION` vs a number).

This tool's visitor maps a successful parse to a tagged CST, then the
mapper (`theories/IntakeWalker.v` + `theories/IntakeAngles.v`) emits
an SHC bag or a named Intake Decline. Grammar accept ≠ valid geometry
≠ cooked graph. CircUnknown well-formed CS is `MkCirc`, not leftover.
