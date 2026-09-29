#requires -Version 5
# Thin smoke: ANTLR C# visitor → bag | named Decline. Mirrors IntakeWalker.v.
# House style: $ErrorActionPreference='Stop'. Same cases as the retired Java smoke.sh.
# Not an oracle keyword (ADR-0006). Engines later test the bag, not the string.
#
#   pwsh ./tools/WktIntakeWalker/smoke.ps1
#   dotnet cake --target=WktIntakeWalker
#
# This script was drafted with AI assistance; human review remains required.

[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
# Decline is a successful smoke observation (exit 3). Do not treat native
# non-zero as a terminating error for the walker CLI.

$root = $PSScriptRoot
$proj = Join-Path $root 'WktIntakeWalker.csproj'

function Find-DotNet {
    if (Get-Command dotnet -ErrorAction SilentlyContinue) {
        return (Get-Command dotnet).Source
    }
    foreach ($c in @(
            (Join-Path $env:HOME '.dotnet/dotnet'),
            (Join-Path $env:USERPROFILE '.dotnet\dotnet'),
            '/usr/share/dotnet/dotnet'
        )) {
        if ($c -and (Test-Path $c)) {
            $rootDir = Split-Path $c
            $env:DOTNET_ROOT = $rootDir
            $env:PATH = "$rootDir$([IO.Path]::PathSeparator)$env:PATH"
            return $c
        }
    }
    throw "dotnet not found. Install the .NET 10 SDK (same TFM as tests/CurveOracleBugHunt)."
}

& (Join-Path $root 'generate.ps1')
$dotnet = Find-DotNet
Write-Host "dotnet build $proj" -ForegroundColor Cyan
& $dotnet build $proj --nologo
if ($LASTEXITCODE -ne 0) { throw "dotnet build failed (exit $LASTEXITCODE)" }
$dll = Join-Path $root 'bin/Debug/net10.0/WktIntakeWalker.dll'
if (-not (Test-Path $dll)) { throw "missing $dll after build" }

function Invoke-Intake {
    param([Parameter(ValueFromRemainingArguments = $true)][string[]]$Wkt)
    $prev = $ErrorActionPreference
    $ErrorActionPreference = 'Continue'
    try {
        $out = & $dotnet $dll @Wkt
    }
    finally {
        $ErrorActionPreference = $prev
    }
    if ($null -eq $out) { return '' }
    if ($out -is [array]) { $out = $out[-1] }
    return ([string]$out).TrimEnd("`r", "`n")
}

$fail = 0
function Check {
    param([string]$Want, [string[]]$Wkt)
    $got = Invoke-Intake -Wkt $Wkt
    # dotnet run may prefix MSBuild noise; take the last non-empty line.
    $lines = @($got -split '[\r\n]+' | Where-Object { $_.Length -gt 0 })
    if ($lines.Count -gt 0) { $got = $lines[-1] }
    if ($got -ne $Want) {
        Write-Host "FAIL expected: $Want"
        Write-Host "         got: $got"
        $script:fail = 1
    }
    else {
        Write-Host "OK $Want"
    }
}

Check 'BAG hens=0 pts=0 0 chickens=' @('POINT (0 0)')
Check 'BAG hens=0,1 pts=0 0;2 0 chickens=0-1:MkChord' @('LINESTRING (0 0, 2 0)')
Check 'BAG hens=0,1,2 pts=0 0;2 0;0 0 chickens=0-1:MkChord,1-2:MkChord' @('LINESTRING (0 0, 2 0, 0 0)')
Check 'BAG hens=0,1 pts=5 0;0 5 chickens=0-1:MkCirc:quarter' @('CIRCULARSTRING (5 0, 3 4, 0 5)')
Check 'DECLINE ID_CsClosedDegenerate' @('CIRCULARSTRING (5 0, 0 5, 5 0)')
Check 'BAG hens=0,1 pts=5 0;-5 0 chickens=0-1:MkCirc:half,1-0:MkCirc:half' @('CIRCLE (5 0, 0 5, -5 0)')
Check 'BAG hens=0,1,2,3 pts=0 0;5 0;5 0;0 5 chickens=0-1:MkChord,2-3:MkCirc:quarter' `
    @('COMPOUNDCURVE ((0 0, 5 0), CIRCULARSTRING (5 0, 3 4, 0 5))')
Check 'BAG hens=0,1 pts=0 0;3 1 chickens=0-1:MkCirc' @('CIRCULARSTRING (0 0, 2 0, 3 1)')
Check 'BAG hens=0,1 pts=0 0;2 4 chickens=0-1:MkCirc:half,1-0:MkCirc:half' @('CIRCLE (0 0, 2 0, 3 1)')
Check 'BAG hens=0,1,2 pts=0 0;2 0;4 0 chickens=0-1:MkCirc,1-2:MkCirc' @('CIRCULARSTRING (0 0, 1 1, 2 0, 3 1, 4 0)')
Check 'DECLINE ID_Collinear' @('CIRCULARSTRING (0 0, 1 0, 2 0)')
Check 'DECLINE ID_DuplicateControl' @('CIRCULARSTRING (0 0, 0 0, 1 1)')
Check 'DECLINE ID_BadPointCount' @('CIRCULARSTRING (0 0, 1 0)')
Check 'DECLINE ID_Empty' @('CIRCULARSTRING EMPTY')
Check 'BAG hens=0,1 pts=0 0;2 0 chickens=0-1:MkChord' @('GEODESICSTRING (0 0, 2 0)')
Check 'DECLINE ID_Empty' @('GEODESICSTRING EMPTY')
Check 'DECLINE ID_BadPointCount' @('GEODESICSTRING (0 0)')
Check 'BAG hens=0,1,2,3 pts=0 0;5 0;5 0;7 0 chickens=0-1:MkChord,2-3:MkChord' `
    @('COMPOUNDCURVE ((0 0, 5 0), GEODESICSTRING (5 0, 7 0))')

# Famous Science/arXiv 1804.07389 fixtures (claimId 0007-famous-geodesicstring).
# Bag-string of GEODESICSTRING equals LINESTRING on the same two points.
# Not an Earth-length / ETOPO1 / ellipsoid / WKB-13 claim.
function Check-SameLsBag {
    param([string]$Label, [string]$WktG, [string]$WktLs)
    $gotG = Invoke-Intake -Wkt @($WktG)
    $gotLs = Invoke-Intake -Wkt @($WktLs)
    $linesG = @($gotG -split '[\r\n]+' | Where-Object { $_.Length -gt 0 })
    $linesLs = @($gotLs -split '[\r\n]+' | Where-Object { $_.Length -gt 0 })
    if ($linesG.Count -gt 0) { $gotG = $linesG[-1] }
    if ($linesLs.Count -gt 0) { $gotLs = $linesLs[-1] }
    if ($gotG -ne $gotLs) {
        Write-Host "FAIL $Label bags differ"
        Write-Host "  GEODESICSTRING: $gotG"
        Write-Host "  LINESTRING:     $gotLs"
        $script:fail = 1
    }
    elseif ($gotG -notlike 'BAG*chickens=0-1:MkChord') {
        Write-Host "FAIL $Label expected BAG ... chickens=0-1:MkChord"
        Write-Host "         got: $gotG"
        $script:fail = 1
    }
    else {
        Write-Host "OK $Label $gotG"
    }
}
# Exact decimal pretty-print is runtime-format, not the letter. Equality
# of the two WKT bag-strings (MkChord-only) is the smoke QED.
Check-SameLsBag 'famous-water' `
    'GEODESICSTRING (66.6666666667 25.2833333333, 162.2333333333 58.6166666667)' `
    'LINESTRING (66.6666666667 25.2833333333, 162.2333333333 58.6166666667)'
Check-SameLsBag 'famous-land' `
    'GEODESICSTRING (118.6333333333 24.55, -8.9166666667 37.0333333333)' `
    'LINESTRING (118.6333333333 24.55, -8.9166666667 37.0333333333)'
Check 'DECLINE ID_SpiralCurve' @('SPIRALCURVE EMPTY')
Check 'BAG hens=0,1 pts=0 0;80 5.333333333333333 chickens=0-1:MkClothoid' @('CLOTHOID (0, 0.005, 80)')
Check 'BAG hens=0,1 pts=0 0;80 5.333333333333333 chickens=0-1:MkClothoid' `
    @('CLOTHOID (REFERENCELOCATION AFFINEPLACEMENT (LOCATION (0 0), REFERENCEDIRECTIONS (VECTOR (1 0), VECTOR (0 1))), SCALEFACTOR 100, STARTDISTANCE 0, ENDDISTANCE 50)')
Check 'BAG hens=0,1,2,3,4,5 pts=0 0;100 0;0 0;80 5.333333333333333;0 0;80 5.333333333333333 chickens=0-1:MkChord,2-3:MkClothoid,4-5:MkClothoid' `
    @('COMPOUNDCURVE ((0 0, 100 0), CLOTHOID (0, 0.005, 80), CLOTHOID (REFERENCELOCATION AFFINEPLACEMENT EMPTY, SCALEFACTOR 100, STARTDISTANCE 0, ENDDISTANCE 50))')

if ($fail -ne 0) {
    Write-Host 'intake walker smoke FAILED'
    exit 1
}
Write-Host 'intake walker smoke OK'
