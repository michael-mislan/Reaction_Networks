# Rest–rhythm bistability and single-rate switching — source folder

Final PDF: `../Rest_Rhythm_Bistability_Single_Rate_Switching_Phosphorylation.pdf` (copy of `main.pdf`).
Author/affiliation are intentionally blank: set `\PaperAuthor`, `\PaperAffiliation` at the top of `main.tex`.

## Build the paper

MiKTeX binaries: `%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`.

```bash
pdflatex -interaction=nonstopmode main.tex
bibtex main
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```

`main.tex` inputs `tables/*.tex` (generated) and `figures/*.pdf` (generated); both are checked in, so the
paper builds without Python. For arXiv, upload `main.tex`, `main.bbl`, `refs.bib`, `tables/`, `figures/*.pdf`.

## Regenerate everything (Python 3.11 venv of the repository: numpy, scipy, mpmath, sympy, matplotlib)

| step | command | time | output |
|---|---|---|---|
| 1 | `python make_data.py` | 2–3 min | `data/numerics.json`, `data/cycles.npz`, `data/branch.npz` (needs the checked-in seeds `data/_stable.npz`, `data/_unstable.npz`: the attracting cycle from a large kick along Re q, the unstable cycle from a 30-step basin bisection along the same ray followed by shooting; see `numerics.py`) |
| 2 | `python make_switch_demo.py` | 1 min | `data/switch_demo.{json,npz}` |
| 3 | `python rank_all_inputs.py` | 10 s | `data/rank_all_inputs.json` — interval Kalman rank for all 18 rates |
| 4 | `python validate_orbit.py witness` | ~17 min | `certificates/orbit_certificate_witness.json` — second, independent CAP of the witness orbit |
| 5 | `python make_tables.py` | 1 s | `tables/*.tex` |
| 6 | `python make_figures.py` | 1 min | `figures/fig_*.pdf` |
| 7 | `python check_paper.py` | 10 s | recomputes/compares every number printed in the paper |

## What is what

* `clock.py` — model from the literal reaction list (via `phos.Model`), binary64 chart field, and an
  independent plain-power centre-manifold normal-form recurrence (mpmath). Shares no code with the workspace certificate.
* `phos.py`, `interval_arithmetic.py` — exact model builder and rational-interval Hopf certifier, copied unchanged
  from the companion paper `Attracting_Oscillations_Distributive_Phosphorylation_arxiv`.
* `validate_orbit.py`, `companion_numerics.py` — multiple-shooting Newton–Kantorovich validator adapted from the companion paper.
* `workspace_certificates/` — copies of the research-workspace certificate chain
  (`problem_workspaces/RAF_switchable_phosphorylation_clock`): `local_certificate.py` (generalized Hopf),
  `finite_source.py`, `sparse_fourier_pilot.py --certify`, `finite_geometry_certificate.py`,
  `attraction_certificate.py`, `single_input_rank_certificate.py`, `sink_capture_certificate.py`, their JSON outputs,
  `replay.py`, and the three Lean modules. The 190 MB `finite_fourier_inverse.npz` is NOT copied; it is regenerated
  by the Fourier stage in the workspace. Replay from the repository root:
  `.venv\Scripts\python.exe scripts/process_guard.py run --timeout 900 --owner-label CLOCK-replay -- <python> problem_workspaces/RAF_switchable_phosphorylation_clock/replay.py`
* `data/rational_patch.json`, `data/finite_source_exact.json` — the exact sources (Tables 4 and 5 of the paper).

## Evidence labels used in the paper

C conventional proof · I interval / error-bounded computation · K Lean · N numerics only.
Theorems 1.1–1.3 rest on C and I. Section 5.5 (switching at the finite witness) is N only.
