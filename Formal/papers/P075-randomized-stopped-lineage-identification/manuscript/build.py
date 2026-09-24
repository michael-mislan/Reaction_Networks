"""Build the manuscript: pdflatex, bibtex, pdflatex x2, then report warnings."""
import subprocess, shutil, sys, os, json, hashlib
from pathlib import Path
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
CAND = [os.environ.get('PDFLATEX'),
        str(Path(os.environ.get('LOCALAPPDATA', '')) / 'Programs/MiKTeX/miktex/bin/x64/pdflatex.exe'),
        shutil.which('pdflatex')]
BIB = [str(Path(os.environ.get('LOCALAPPDATA', '')) / 'Programs/MiKTeX/miktex/bin/x64/bibtex.exe'),
       shutil.which('bibtex')]
tex = next((c for c in CAND if c and Path(c).exists()), None)
bib = next((c for c in BIB if c and Path(c).exists()), None)
assert tex and bib, 'pdflatex/bibtex not found'

# Lint: catch control-character or escape damage that silently deletes a macro.
import re
import io as _io
src = _io.open(HERE / 'main.tex', encoding='utf-8', newline='').read()
assert '\r' not in src, 'stray carriage return in main.tex'
orphan = [m.group(0) for m in
          re.finditer(r'(?<![\\A-Za-z])(ef|eqref|abel|ite|extbf|ection)\{', src)]
assert not orphan, 'orphaned macro name (lost backslash): %s' % orphan
for cmd in ('ref', 'eqref', 'label', 'cite'):
    for m in re.finditer(r'\\' + cmd + r'\{([^}]*)\}', src):
        assert m.group(1).strip(), 'empty \\%s{}' % cmd

def run(cmd, log):
    r = subprocess.run(cmd, cwd=HERE, capture_output=True, text=True, timeout=300)
    (HERE / log).write_text(r.stdout + '\n' + r.stderr, encoding='utf-8')
    return r

r = run([tex, '--disable-installer', '-interaction=nonstopmode', 'main.tex'], 'pass1.log')
run([bib, 'main'], 'bibtex.log')
for i in (2, 3):
    r = run([tex, '--disable-installer', '-interaction=nonstopmode', 'main.tex'], 'pass%d.log' % i)
log = (HERE / 'main.log').read_text(errors='replace')
bad = [s for s in log.splitlines()
       if ('Overfull' in s or 'Underfull' in s or 'undefined' in s.lower()
           or 'Warning' in s) and 'Font Warning' not in s]
pdf = HERE / 'main.pdf'
assert pdf.exists(), 'no PDF produced'
assert '\bibdata' not in '' and 'There were undefined references' not in log, 'undefined references'
man = dict(timestamp=datetime.now(timezone.utc).isoformat(),
           pdf=str(pdf), sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),
           pages=log.count('] ['), warnings=bad)
(HERE / 'build_manifest.json').write_text(json.dumps(man, indent=1))
print('\n'.join(bad) if bad else 'no layout or reference warnings')
print('PDF:', pdf, pdf.stat().st_size, 'bytes')
