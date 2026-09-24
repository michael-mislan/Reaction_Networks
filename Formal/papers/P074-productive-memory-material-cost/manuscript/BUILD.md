# Build, audit and submission notes

**Paper.** *The material and kinetic cost of productive chemical memory: exact
frontiers for support and proportion encodings.* 26 pages. Author, affiliation
and PDF author metadata are intentionally blank.

This package **merges and supersedes** two separate 7-page manuscripts dated
17 September 2026, *The Material Cost of Productive Chemical Memory* (the
32-unit support-memory frontier) and *Productive Chemical Heredity with Finite
Resources* (the 415-unit cooperative construction). Neither is cited as prior
work: the merged paper presents both sources as its own, which is why the two
self-citations that appeared in an early draft were removed.

## What is new here, relative to the two source drafts

| Result | Status in the drafts | Status here |
|---|---|---|
| Robust minimum $K=32$ over $\kappa\in[10,20]$ | proved | reproduced from an independent implementation (App. B) |
| Allocation-bias tolerance | $\theta\in[0.495,0.505]$, by a payoff-perturbation bound | $\theta\in[0.39,0.61]$, by re-running the certificate on the biased payoff; $\theta=0.38$ **excluded** |
| Rate-constant uncertainty | not addressed | simultaneous independent $\pm1/300$ box on all six constants, Thm 4.9 |
| Untied complex branching | not addressed | **new frontier $K=42$**, Thm 4.10; non-monotonicity in the release rate; mechanism (Table 4) |
| Partition constant for the 415-unit source | $99957/100000$ (union bound) | exact endpoint minimum $\Phi_*=0.999712941541084\ldots$ |
| Per-cycle / ten-cycle guarantee | $0.9995$ / $0.995$ | $0.9997$ / $0.997$ |
| Is 415 optimal? | open — a construction | **no: the class frontier is 253 core units**, Thm 5.8 |
| Reliability scaling of that class | not addressed | exact frontier over five decades; $\Theta(\log(1/\delta))$ proved, Thm 5.9 |
| Corridor cascade / $m$ levels | not addressed | triangular-number balance law, per-level cost $4k^2z^2$, cubic in $m$ |
| Encoding comparison | the two papers were disjoint | Table 5: 32 vs 231 at one specification |

Two errors in the drafts were found and corrected while preparing this package.
The reported value of the clock constant $r_*$ was computed from a 40-term
Taylor sum while the displayed formula used the cruder bound $e^{20}>4\times10^8$;
the paper now prints the value the displayed formula actually gives,
$0.999999497500251\ldots$, and the corresponding joint bound
$0.999712439185582\ldots$. Molecularities quoted for the scaling table were
each off by one because the fuel token was not counted.

## Files

| Path | Role |
|---|---|
| `main.tex` | The manuscript. Self-contained: the bibliography is an inline `thebibliography`, so no BibTeX pass is needed. |
| `refs.bib` | The same sixteen references in BibTeX form, for convenience. Not used by the current build. |
| `figures/*.pdf` | The three included vector figures. Figure 1 is inline TikZ and needs no file. |
| `figures.py` | Regenerates the figures from `data/*.json`. Needs matplotlib only. |
| `check_paper.py` | Exact audit of every printed number (see below). |
| `scripts/` | The five computational scripts; see §8 of the paper for what each produces. |
| `data/*.json` | Their recorded output. |
| `companion/proofs/` | The ten Lean modules, in their two namespaces. |
| `companion/verification/` | Strict verification receipts with axiom reports. |
| `qa/` | Page rasterisations used for the visual pass. |

## Building

MiKTeX binaries on this machine live under
`%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`.

```bash
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

Three passes are needed for the table of contents and forward references. The
build is clean: no overfull or underfull boxes, no undefined references or
citations. **Always check `main.log`** — a full disk makes pdflatex silently
drop `main.aux` and emit a PDF full of `??` references.

Packages used: `geometry`, `fontenc`, `inputenc`, `lmodern`, `amsmath`,
`amssymb`, `amsthm`, `booktabs`, `array`, `longtable`, `graphicx`, `microtype`,
`tikz` (libraries `arrows.meta`, `positioning`, `calc`), `hyperref`. All are
standard on arXiv.

## Auditing the numbers

```bash
python check_paper.py          # fast: uses the recorded data/
python check_paper.py --full   # re-runs every script first (~8 minutes)
```

At the time of writing this reports:

```
238 printed values reproduced exactly.
```

The proportion-memory side is recomputed inside `check_paper.py` from scratch
in exact rational arithmetic with the standard library alone, including a
brute-force re-verification of the endpoint reduction lemma, the four cascade
identities, and the concave rate-span argument. The support-memory side is
checked against `data/frontier_support.json`, which `--full` regenerates.

## Regenerating artifacts

From the repository root `E:\Erdos Problems`, with the canonical interpreter:

```bash
./.venv/Scripts/python.exe scripts/process_guard.py run --timeout 900 \
  --owner-label MEMCOST-PAPER -- "E:\Erdos Problems\.venv\Scripts\python.exe" \
  key_results/RAFs/Material_Kinetic_Cost_Productive_Chemical_Memory_arxiv/scripts/frontier_support.py
```

`frontier_support.py` is the long one (about six minutes; it runs 28 budgets of
the untied vertex). The other four scripts finish in seconds. `figures.py` is
run from the package directory.

## Re-verifying the Lean development

From the repository root, using its pinned Lean 4.30.0 / Mathlib workspace:

```bash
./.venv/Scripts/python.exe scripts/verify_proof.py \
  proofs/UsefulChemicalMemoryCost/Resolution.lean --timeout 900 \
  --declaration UsefulChemicalMemoryCost.envelope_le_kernel \
  --declaration UsefulChemicalMemoryCost.robust_poisson_lower \
  --declaration UsefulChemicalMemoryCost.complement_upper \
  --declaration UsefulChemicalMemoryCost.material_necessary \
  --declaration UsefulChemicalMemoryCost.publication_arithmetic
```

```bash
./.venv/Scripts/python.exe scripts/verify_proof.py \
  proofs/ProductiveChemicalHeredity/Main.lean --timeout 900 \
  --declaration ProductiveChemicalHeredity.exact_closed_pair \
  --declaration ProductiveChemicalHeredity.forward_rate_lower \
  --declaration ProductiveChemicalHeredity.reverse_rate_upper \
  --declaration ProductiveChemicalHeredity.complementary_binomial_law \
  --declaration ProductiveChemicalHeredity.endpoint_tail_certificate \
  --declaration ProductiveChemicalHeredity.declared_arithmetic_and_budget
```

Both were re-run for this package and returned `verified: true`, exit code 0,
with every exported declaration depending only on `propext`,
`Classical.choice` and `Quot.sound`. Do not run `lake update`.

## arXiv submission

Upload `main.tex` together with the `figures/` directory. Nothing else is
required: there is no `.bbl`, no BibTeX pass, and all figure paths are
relative. `refs.bib`, `figures.py`, `check_paper.py`, `scripts/`, `data/`,
`companion/` and `qa/` are development and reproducibility material, not part
of the TeX build; ship them as a separate archive or repository link.

Before an actual submission, fill in the author, affiliation, licence,
acknowledgements and a permanent code/version reference, and pick the subject
categories after checking the current definitions. Suggested primary category:
`q-bio.MN` (molecular networks), with cross-lists to `math.PR` (probability),
`cs.LO` (logic in computer science, for the formal verification component) and
`nlin.AO` (adaptation and self-organizing systems).
