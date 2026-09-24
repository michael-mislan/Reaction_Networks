# Exposure and amplitude limits for eradicating populations with inherited cellular states

arXiv-style source package. Author and affiliation fields are intentionally
blank in `main.tex`.

## Build

MiKTeX `pdflatex` + `bibtex` (no `latexmk`, which needs Perl on this machine):

```
pdflatex -interaction=nonstopmode main.tex
bibtex main
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```

`build.sh` runs the same four commands and then checks the log for overfull
boxes and undefined references. The produced file is `main.pdf` (26 pages).

## Layout

```
main.tex                 preamble, abstract, includes
sections/                one file per section and appendix
references.bib           bibliography
tables/budget_rows.tex   Table 1 (two-site budget rows)
figures/                 budget.pdf, policy.pdf, sites.pdf
data/                    exact certificates and enclosure inputs
scripts/                 source reconstruction, certificate generation, checkers
qa/                      page renders used for layout inspection
```

## Data files

| file | contents |
| --- | --- |
| `site_certificates.json` | everything in Section 7: critical-erasure brackets, Collatz--Wielandt witnesses at `e=3/10`, contraction weights at `e=1/2`, baseline exposure certificates, amplitude floors, added-death thresholds |
| `source_certificates.json` | two-site certificates, the `b_P in [.08,.1]` scenario family, the four-site row |
| `validated_policy.json` | exact inputs and accumulated radius of the dyadic Taylor enclosure behind eq. (24) |
| `figure_data.json` | curves plotted in Figures 1 and 2 |

## Reproduction

```
python scripts/verify_certificates.py     # replays every exact check in Section 7
python scripts/make_certificates.py       # regenerates site_certificates.json (~2.5 min)
python scripts/site_figure.py             # regenerates figures/sites.pdf
python scripts/exact_source_checks.py     # two-site rational residuals (Section 6)
python scripts/validated_pgf.py           # dyadic enclosure behind eq. (24)
```

`verify_certificates.py` reconstructs every source matrix from the chemistry,
the binomial allocation law and the death rule, and checks every inequality with
`fractions.Fraction`. Nothing floating enters a verdict; floating arithmetic is
used only to propose candidate vectors and to produce the clearly labelled
diagnostics (Remark 7.2, the open markers in Figure 3, the curves in Figure 2).
Requires Python 3.11, `numpy`, `matplotlib` (figures only).

Expected final line of `verify_certificates.py`: `ALL CHECKS PASSED`.

## Relation to the earlier two-site manuscript

This paper merges and supersedes *Exposure limits for eradicating populations
with inherited cellular states* (12 pages, 20 September 2026). Retained:
the exposure floor and its corollaries, the logarithmic order law, the
finite-time floor, the two-site source and its certificates, the validated
pulse at exposure 11.6, the RR preparation counterexample, the slower-division
scenario family, and the PK/PD bounds. New in this version:

* Theorem 4.1, the amplitude floor, and the three-obstruction framing.
* Section 7: exact critical-erasure brackets for `2 <= N <= 8`, the certified
  amplitude floors showing that no policy of amplitude `.29` eradicates from
  five sites on, baseline exposure certificates for every `N`, and the
  large-`N` diagnostics.
* Section 7.4: the added-death actuator, its `N`-uniform threshold
  `b - d_prot`, the dimension-free sufficient exposure `1.45 log(n/delta)`, and
  the resulting near-sharp exposure constant.
* Remark 6.1: an optimized two-site exposure certificate improving the floor by
  0.54%, which shows the remaining constant gap is not a certificate artefact.
