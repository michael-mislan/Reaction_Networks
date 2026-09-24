#!/usr/bin/env bash
# Build main.pdf with MiKTeX pdflatex/bibtex and check the log.
set -e
cd "$(dirname "$0")"
export PATH="$LOCALAPPDATA/Programs/MiKTeX/miktex/bin/x64:$PATH"
pdflatex -interaction=nonstopmode main.tex > /dev/null
bibtex main > /dev/null
pdflatex -interaction=nonstopmode main.tex > /dev/null
pdflatex -interaction=nonstopmode main.tex > /dev/null
echo "--- log check ---"
if grep -E "Overfull|undefined|LaTeX Warning: Citation|LaTeX Warning: Reference" main.log; then
  echo "LOG NOT CLEAN"; exit 1
fi
grep -c "" /dev/null || true
grep "Output written" main.log
echo "log clean"
