#requires -Version 5
# SqlMmWktAngleHunt — chart angles vs Math.Atan2, plus SQLMM_WKT.
# House style: $ErrorActionPreference='Stop'. claimId: none (tools).
#
#   pwsh ./tests/SqlMmWktAngleHunt/hunt.ps1
#   dotnet cake --target=SqlMmWktAngleHunt
#
# This script was drafted with AI assistance; human review remains required.

[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
if ($PSVersionTable.PSVersion.Major -ge 7) {
    $PSNativeCommandUseErrorActionPreference = $true
}

$here = $PSScriptRoot
$repo = (Resolve-Path (Join-Path $here '../..')).Path
$proj = Join-Path $here 'SqlMmWktAngleHunt.csproj'

function Find-DotNet {
    if (Get-Command dotnet -ErrorAction SilentlyContinue) {
        return (Get-Command dotnet).Source
    }
    foreach ($c in @(
            (Join-Path $env:HOME '.dotnet/dotnet'),
            '/usr/share/dotnet/dotnet'
        )) {
        if ($c -and (Test-Path $c)) {
            $root = Split-Path $c
            $env:DOTNET_ROOT = $root
            $env:PATH = "$root$([IO.Path]::PathSeparator)$env:PATH"
            return $c
        }
    }
    throw "dotnet not found. Install the .NET 10 SDK."
}

Push-Location $repo
try {
    $dotnet = Find-DotNet
    & $dotnet run --project $proj --nologo
    if ($LASTEXITCODE -ne 0) { throw "SqlMmWktAngleHunt exited $LASTEXITCODE" }
}
finally {
    Pop-Location
}
