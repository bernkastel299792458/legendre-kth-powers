param(
    [Parameter(Mandatory=$true)][string]$File,
    [string]$DependencyRoot,
    [string]$LeanExecutable
)
$ErrorActionPreference = 'Stop'
$leanRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../lean'))
if (-not $DependencyRoot) { $DependencyRoot = Join-Path $leanRoot '.lake/packages' }
if (-not (Test-Path -LiteralPath $DependencyRoot)) {
    throw 'Dependency cache missing. Run lake update and lake exe cache get in proof/lean, or provide -DependencyRoot.'
}
if (-not $LeanExecutable) {
    $leanCommand = Get-Command lean -ErrorAction SilentlyContinue
    if ($leanCommand) { $LeanExecutable = $leanCommand.Source }
    else { $LeanExecutable = Join-Path $env:USERPROFILE '.elan/bin/lean.exe' }
}
$sourceFile = [IO.Path]::GetFullPath((Join-Path $leanRoot $File))
if (-not $sourceFile.StartsWith($leanRoot + [IO.Path]::DirectorySeparatorChar, [StringComparison]::OrdinalIgnoreCase)) {
    throw 'Source file must be inside this Lean project.'
}
$buildLib = Join-Path $leanRoot '.lake/build/lib/lean'
$moduleRelative = [IO.Path]::ChangeExtension($File, '.olean')
$outputFile = Join-Path $buildLib $moduleRelative
New-Item -ItemType Directory -Force -Path ([IO.Path]::GetDirectoryName($outputFile)) | Out-Null
$searchPaths = @($buildLib, $leanRoot)
foreach ($dependency in Get-ChildItem -LiteralPath $DependencyRoot -Directory) {
    $library = Join-Path $dependency.FullName '.lake/build/lib/lean'
    if (Test-Path -LiteralPath $library) { $searchPaths += $library }
}
$env:LEAN_PATH = $searchPaths -join [IO.Path]::PathSeparator
Push-Location $leanRoot
try {
    & $LeanExecutable -DautoImplicit=false -o $outputFile $File
    if ($LASTEXITCODE -ne 0) { throw "Lean failed for $File (exit $LASTEXITCODE)" }
} finally { Pop-Location }
