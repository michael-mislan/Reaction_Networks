param([switch]$RegenerateFigures)
$ErrorActionPreference = 'Stop'
$sourceDirectory = $PSScriptRoot
$repoDirectory = (Resolve-Path (Join-Path $sourceDirectory '../../..')).Path
$miktexDirectory = Join-Path $env:LOCALAPPDATA 'Programs/MiKTeX/miktex/bin/x64'
$latexExecutable = Join-Path $miktexDirectory 'pdflatex.exe'
$bibtexExecutable = Join-Path $miktexDirectory 'bibtex.exe'
if (-not (Test-Path -LiteralPath $latexExecutable)) { $latexExecutable = (Get-Command pdflatex).Source }
if (-not (Test-Path -LiteralPath $bibtexExecutable)) { $bibtexExecutable = (Get-Command bibtex).Source }
if ($RegenerateFigures) {
    & (Join-Path $repoDirectory '.venv/Scripts/python.exe') (Join-Path $sourceDirectory 'reproduce.py')
    if ($LASTEXITCODE -ne 0) { throw 'Figure/arithmetic reproduction failed.' }
    & (Join-Path $repoDirectory '.venv/Scripts/python.exe') (Join-Path $sourceDirectory 'make_workflow.py')
    if ($LASTEXITCODE -ne 0) { throw 'Workflow figure generation failed.' }
}
Push-Location $sourceDirectory
try {
    & $latexExecutable -interaction=nonstopmode -halt-on-error main.tex
    if ($LASTEXITCODE -ne 0) { throw 'First LaTeX pass failed.' }
    & $bibtexExecutable main
    if ($LASTEXITCODE -ne 0) { throw 'BibTeX failed.' }
    foreach ($pass in 1..2) {
        & $latexExecutable -interaction=nonstopmode -halt-on-error main.tex
        if ($LASTEXITCODE -ne 0) { throw "LaTeX pass $pass failed." }
    }
    $buildLog = Get-Content -Raw -LiteralPath 'main.log'
    if ($buildLog -match 'Overfull|There were undefined|Citation .* undefined|Reference .* undefined|Infinite glue|LaTeX Warning') {
        throw 'The document log has an unresolved layout/reference issue.'
    }
    Copy-Item -LiteralPath 'main.pdf' -Destination (Join-Path $sourceDirectory '../ASSAYS_How_to_Design_an_Assay.pdf') -Force
} finally { Pop-Location }
