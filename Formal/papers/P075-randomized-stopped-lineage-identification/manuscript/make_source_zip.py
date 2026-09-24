"""Bundle the minimal arXiv submission: main.tex, refs.bib, main.bbl, figures."""
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
out = HERE.parent / 'Randomized_Stopped_Lineage_Identification_arxiv_source.zip'
files = ['main.tex', 'refs.bib', 'main.bbl'] + sorted(
    str(p.relative_to(HERE)) for p in (HERE / 'figures').glob('*.pdf'))
with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED) as z:
    for f in files:
        z.write(HERE / f, Path(f).as_posix())
print(out, out.stat().st_size, 'bytes')
print(zipfile.ZipFile(out).namelist())
