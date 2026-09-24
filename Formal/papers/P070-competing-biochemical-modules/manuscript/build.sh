#!/usr/bin/env bash
# Clean LaTeX build in a scratch directory; copies main.pdf/main.bbl/main.log back here
# and the titled PDF to the parent folder.
set -e
here="$(cd "$(dirname "$0")" && pwd)"
export PATH="$LOCALAPPDATA/Programs/MiKTeX/miktex/bin/x64:$PATH"
B="$(mktemp -d)"
cp "$here/main.tex" "$here/refs.bib" "$B"; cp -r "$here/figures" "$B"
cd "$B"
pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null || { grep -A8 "^!" main.log; exit 1; }
bibtex main >/dev/null
pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null || { grep -A8 "^!" main.log; exit 1; }
pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null || { grep -A8 "^!" main.log; exit 1; }
if grep -E "Overfull|undefined|multiply defined|^!" main.log; then echo "LOG NOT CLEAN"; fi
test -s main.aux
cp main.pdf main.bbl main.log "$here"
cp main.pdf "$here/../Compatibility_Competing_Biochemical_Modules_Capacity_Recovery_Finite_Operation.pdf"
echo "built: $(pdfinfo main.pdf 2>/dev/null | grep Pages)"
