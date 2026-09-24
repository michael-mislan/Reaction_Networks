$ErrorActionPreference = 'Stop'
# Exact replay of the paper's constants, regeneration of both figures, then a
# clean LaTeX build in a scratch directory; the PDF is copied back here and to
# the parent results folder.
$here = $PSScriptRoot
$python = Resolve-Path (Join-Path $here '..\..\..\.venv\Scripts\python.exe')
$env:Path = "$env:LOCALAPPDATA\Programs\MiKTeX\miktex\bin\x64;$env:Path"

Push-Location $here
try {
    & $python check_paper.py
    if ($LASTEXITCODE -ne 0) { throw 'check_paper.py failed.' }
    & $python make_figures.py
    if ($LASTEXITCODE -ne 0) { throw 'make_figures.py failed.' }
    $build = Join-Path $env:TEMP ('rcss_build_' + [guid]::NewGuid().ToString('N').Substring(0, 8))
    New-Item -ItemType Directory -Force $build | Out-Null
    Copy-Item main.tex, refs.bib $build
    Copy-Item figures $build -Recurse
    Push-Location $build
    try {
        # MiKTeX writes an update nag to stderr; with ErrorActionPreference=Stop
        # PowerShell would turn that into a terminating NativeCommandError.
        $ErrorActionPreference = 'Continue'
        pdflatex -interaction=nonstopmode -halt-on-error main.tex | Out-Null
        bibtex main | Out-Null
        pdflatex -interaction=nonstopmode -halt-on-error main.tex | Out-Null
        pdflatex -interaction=nonstopmode -halt-on-error main.tex | Out-Null
        $ErrorActionPreference = 'Stop'
        if ($LASTEXITCODE -ne 0) { throw ('pdflatex failed; see main.log in ' + $build) }
        if (-not (Test-Path main.aux)) { throw ('main.aux missing; the build is not trustworthy: ' + $build) }
        $log = Get-Content main.log -Raw
        foreach ($pat in 'LaTeX Warning: Reference', 'LaTeX Warning: Citation', 'Overfull \hbox', 'undefined') {
            if ($log -match [regex]::Escape($pat)) { Write-Warning ("main.log contains: " + $pat) }
        }
        Copy-Item main.pdf, main.bbl, main.log $here -Force
        Copy-Item main.pdf (Join-Path $here '..\Repeated_Chemical_State_Selection.pdf') -Force
    } finally { Pop-Location }
    Write-Host "Built $build\main.pdf and copied to $here and the parent folder."
} finally { Pop-Location }
