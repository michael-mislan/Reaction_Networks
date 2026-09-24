$ErrorActionPreference = 'Stop'
# Build chain: exact replay of the paper's constants, regeneration of the
# vector figures, then a clean LaTeX build in a scratch directory, then copy the
# PDF back here and to the parent folder.
$here = $PSScriptRoot
$python = Resolve-Path (Join-Path $here '..\..\..\.venv\Scripts\python.exe')
$env:Path = "$env:LOCALAPPDATA\Programs\MiKTeX\miktex\bin\x64;$env:Path"

Push-Location $here
try {
    & $python check_paper.py
    if ($LASTEXITCODE -ne 0) { throw 'check_paper.py failed.' }
    & $python make_figures.py
    if ($LASTEXITCODE -ne 0) { throw 'make_figures.py failed.' }
    $build = Join-Path $env:TEMP ('ffwb_build_' + [guid]::NewGuid().ToString('N').Substring(0, 8))
    New-Item -ItemType Directory -Force $build | Out-Null
    Copy-Item main.tex, refs.bib, diagnostic_table.tex $build
    Copy-Item figures $build -Recurse
    Push-Location $build
    try {
        pdflatex -interaction=nonstopmode main.tex | Out-Null
        bibtex main | Out-Null
        pdflatex -interaction=nonstopmode main.tex | Out-Null
        pdflatex -interaction=nonstopmode -halt-on-error main.tex
        if ($LASTEXITCODE -ne 0) { throw 'pdflatex failed; see main.log in ' + $build }
        Copy-Item main.pdf, main.bbl, main.log $here -Force
        Copy-Item main.pdf (Join-Path $here '..\Reliable_Autocatalytic_Operation_Finite_Fuel_Waste_Bath.pdf') -Force
    } finally { Pop-Location }
    Write-Host "Built $build\main.pdf and copied to $here and the parent folder."
} finally { Pop-Location }
