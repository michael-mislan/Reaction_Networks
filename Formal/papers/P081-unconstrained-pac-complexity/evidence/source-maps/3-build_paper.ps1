$ErrorActionPreference = 'Stop'
$publicationDir = $PSScriptRoot
$projectDir = Split-Path -Parent $publicationDir
$texExe = 'C:\Users\researcher\AppData\Local\Programs\MiKTeX\miktex\bin\x64\pdflatex.exe'
Push-Location $publicationDir
try {
    for ($pass = 1; $pass -le 2; $pass++) {
        & $texExe --disable-installer -interaction=nonstopmode -halt-on-error -jobname=unconstrained_pac_paper paper.tex
        if ($LASTEXITCODE -ne 0) { throw "PDF compilation failed on pass $pass" }
    }
    Copy-Item -LiteralPath (Join-Path $publicationDir 'unconstrained_pac_paper.pdf') -Destination (Join-Path $projectDir 'unconstrained_pac_paper.pdf') -Force
} finally {
    Pop-Location
}
