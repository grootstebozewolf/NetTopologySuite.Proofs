<!-- doc-kind: guide -->
# WktUnicodeIllustrator

ANSI-coloured **Unicode sketches** of spatial cases from WKT — lines **and** SQL/MM curves.

| Layer | Colour | Meaning |
|-------|--------|---------|
| **A** | blue | first input geometry |
| **B** | red | second input geometry |
| **result** | green | operation output (default: intersection) |
| A∩B pixel | magenta | grid cell touched by both inputs (before result paint) |
| **fill** | ░ (input colour) | surface interior; `╳` magenta where both interiors overlap (`--no-fill` to disable) |
| **A-overshoot** | maroon | self-overlap on A (e.g. CIRCULARSTRING that retraces itself) |
| **B-overshoot** | navy | self-overlap on B |

**NTS dependency:** prefers a **project reference** to the sibling curve-aware clone  
`../NetTopologySuite` (`CIRCULARSTRING` / `COMPOUNDCURVE` / `CURVEPOLYGON` in `WKTReader`).  
Override with `-p:NtsProject=...`. Falls back to NuGet 2.6 (lines only) with a build warning;
in that build **curve WKT exits 4** with a message — no chord approximation is ever rendered,
because a degraded picture is worse than no picture.

**Terminal fit:** on a live console the grid auto-shrinks so the frame never
wraps (redirect output to keep the requested `--width`). If the frame's right
edge still drifts on rows containing `●`/`╳`, your terminal renders those
East-Asian-ambiguous glyphs double-width — use a font/terminal that treats
them as narrow (Windows Terminal + Cascadia Mono does).

**Exit codes:** `0` ok · `2` bad args / WKT parse / empty geometry · `3` overshoot or overlay
operation failed · `4` curve WKT without curve support (lines-only NuGet build).

**PNG facsimile:** `--png <path>` additionally writes a PNG of what the terminal
shows — always coloured, rastered with the embedded Cascadia Mono (OFL, see
`assets/`) on the Windows Terminal Campbell palette, long lines wrapped at
max(80, panel width). Deterministic: same inputs → same bytes, so doc images
regenerate instead of being screenshotted.

Curves are **linearized** for draw + overlay (playground curve ops); labels keep native curve WKT.

**Structure glyphs:** after occupancy paint, each cell is remapped from its 8-neighbour
connectivity to box-drawing / diagonal Unicode (`─│┌┐└┘├┤┬┴┼╭╮╰╯╱╲╳●`) — a lightweight
structure-based pass inspired by Xu–Zhang–Wong *Structure-based ASCII Art*, not tone dithering.

## Run

```powershell
# Default demo: diagonals of the 10×10 square crossing at (5 5)
dotnet run --project tools/WktUnicodeIllustrator

# Custom WKT + operation
dotnet run --project tools/WktUnicodeIllustrator -- `
  "LINESTRING (0 0, 10 10)" "LINESTRING (0 10, 10 0)" --op intersection

# Horizontal × vertical
dotnet run --project tools/WktUnicodeIllustrator -- `
  "LINESTRING (0 0, 4 0)" "LINESTRING (2 -2, 2 2)"

# No ANSI (CI logs / monochrome)
dotnet run --project tools/WktUnicodeIllustrator -- --no-color

# Force ANSI even when stdout is redirected (pipes / capture files)
dotnet run --project tools/WktUnicodeIllustrator -- --force-color

# Curves (requires local NTS clone with CircularString WKT)
dotnet run --project tools/WktUnicodeIllustrator -- --demo curve --no-color
dotnet run --project tools/WktUnicodeIllustrator -- --no-color `
  "CIRCULARSTRING (0 0, 5 8, 10 0)" "LINESTRING (0 4, 10 4)"

# Self-overlapping circular strings (overshoot = maroon A / navy B)
dotnet run --project tools/WktUnicodeIllustrator -- --demo overshoot
dotnet run --project tools/WktUnicodeIllustrator -- --demo overshoot --force-color
# disable overshoot paint:
dotnet run --project tools/WktUnicodeIllustrator -- --demo overshoot --no-overshoot

# Automated checks (same CaseIllustrator path as the CLI)
dotnet test tools/WktUnicodeIllustrator.Tests -c Release
```

Requires a UTF-8 terminal (Windows Terminal, modern PowerShell, or `chcp 65001`).

**Legend:** A = blue · B = red · operation result = green · A∩B pixel = magenta.

## How it works (MVP)

1. Parse A and B with NTS `WKTReader`.
2. Compute `A.Intersection(B)` (or another `--op`).
3. Fit a character grid to the joint envelope (aspect-preserving).
4. Rasterize linework with Bresenham + direction glyphs (`─ │ ╱ ╲`).
5. Print twice: inputs only, then with green result overlay.

Polygons stroke their boundary and shade their interior (`░` single, `╳` overlap;
cell-centre point-in-polygon against the linearized surfaces). `--demo venn` shows it;
`--no-fill` reverts to boundary-only.

## Layout

```
tools/WktUnicodeIllustrator/
  Program.cs                 CLI (parses args, prints CaseIllustrator output)
  CaseIllustrator.cs         pure WKT → framed Unicode report (CLI + tests)
  GeometryCurves.cs          NTS curve parse + densify for draw/ops
  Canvas.cs / WorldToGrid.cs / Rasterizer.cs / AnsiRenderer.cs
  WktUnicodeIllustrator.csproj   → ProjectReference local NetTopologySuite
  README.md
tools/WktUnicodeIllustrator.Tests/
  DefaultCrossingTests.cs    line + CircularString structural asserts
```
