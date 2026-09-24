"""Audit that every cross-reference and citation in main.tex resolves, and that
no macro lost its backslash."""
import re, io, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
src = io.open(HERE / 'main.tex', encoding='utf-8', newline='').read()
aux = io.open(HERE / 'main.aux', encoding='utf-8', errors='replace').read()
log = io.open(HERE / 'main.log', encoding='utf-8', errors='replace').read()
bib = io.open(HERE / 'refs.bib', encoding='utf-8').read()

fail = []
labels = set(re.findall(r'\\newlabel\{([^}]*)\}', aux))
used = set(re.findall(r'\\(?:eq)?ref\{([^}]*)\}', src))
missing = sorted(used - labels)
if missing:
    fail.append('references without labels: %s' % missing)

declared = set(re.findall(r'\\label\{([^}]*)\}', src))
unused = sorted(l for l in declared if l not in used)
keys = set(re.findall(r'@\w+\{([^,]+),', bib))
cited = set(k.strip() for g in re.findall(r'\\citep?\{([^}]*)\}', src) for k in g.split(','))
if cited - keys:
    fail.append('citations with no bib entry: %s' % sorted(cited - keys))
uncited = sorted(keys - cited)

if '\r' in src:
    fail.append('stray carriage return in main.tex')
orphan = [m.group(0) for m in re.finditer(r'(?<![\\A-Za-z])(ef|eqref|abel|ite|ection)\{', src)]
if orphan:
    fail.append('orphaned macro names: %s' % orphan)
for bad in ('??', 'Undefined control sequence', 'There were undefined references',
            'Citation ', 'Label(s) may have changed'):
    if bad in log and bad != '??':
        fail.append('log contains %r' % bad)

pages = re.search(r'Output written on main.pdf \((\d+) pages', log)
print('pages:', pages.group(1) if pages else '?')
print('labels declared: %d, referenced: %d' % (len(declared), len(used)))
print('unreferenced labels (harmless):', unused)
print('uncited bib entries:', uncited)
print('overfull/underfull boxes:',
      [l for l in log.splitlines() if 'Overfull' in l or 'Underfull' in l])
if fail:
    print('\nFAILURES:')
    for f in fail:
        print('  ' + f)
    sys.exit(1)
print('\nreference audit clean')
