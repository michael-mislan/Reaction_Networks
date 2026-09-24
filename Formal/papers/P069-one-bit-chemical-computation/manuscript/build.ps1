$ErrorActionPreference = 'Stop'
# Build chain: exact replay of every printed constant, regeneration of the four
# figures, then a clean LaTeX build in a scratch directory; the PDF, .bbl and
# .log are copied back here and the PDF also to the parent folder.
$here = $PSScriptRoot
$python = Resolve-Path (Join-Path $here '..\..\..\.venv\Scripts\python.exe')
$env:Path = "$env:LOCALAPPDATA\Programs\MiKTeX\miktex\bin\x64;$env:Path"

Push-Location $here
try {
    & $python check_paper.py
    if ($LASTEXITCODE -ne 0) { throw 'check_paper.py failed.' }
    & $python make_figures.py
    if ($LASTEXITCODE -ne 0) { throw 'make_figures.py failed.' }

    $build = Join-Path 'E:\ClaudeTemp' ('c1b_build_' + [guid]::NewGuid().ToString('N').Substring(0, 8))
    New-Item -ItemType Directory -Force $build | Out-Null
    Copy-Item main.tex, refs.bib $build
    Copy-Item figures $build -Recurse
    Push-Location $build
    try {
        pdflatex -interaction=nonstopmode main.tex | Out-Null
        bibtex main | Out-Null
        pdflatex -interaction=nonstopmode main.tex | Out-Null
        pdflatex -interaction=nonstopmode -halt-on-error main.tex
        if ($LASTEXITCODE -ne 0) { throw "pdflatex failed; see main.log in $build" }
        if (-not (Test-Path main.aux)) { throw 'main.aux missing: the build was truncated.' }
        $log = Get-Content main.log -Raw
        foreach ($bad in @('Undefined control sequence', 'LaTeX Error',
                           'There were undefined references', 'Citation .* undefined')) {
            if ($log -match $bad) { throw "main.log contains: $bad" }
        }
        Copy-Item main.pdf, main.bbl, main.log $here -Force
        Copy-Item main.pdf (Join-Path $here '..\Certified_One_Bit_Chemical_Computation.pdf') -Force
    } finally { Pop-Location }
    Write-Host "Built $build\main.pdf and copied it to $here and the parent folder."
} finally { Pop-Location }
