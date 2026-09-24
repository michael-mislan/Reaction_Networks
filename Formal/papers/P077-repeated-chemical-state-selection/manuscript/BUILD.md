# Repeated selection of inherited chemical states — source package

Paper: *Repeated selection of inherited chemical states: finite-population
guarantees and a logarithmic horizon law* (26 pages).
Built PDF: `main.pdf`, also copied to `../Repeated_Chemical_State_Selection.pdf`.

Author, affiliation and repository macros are deliberately blank; set
`\PaperAuthor`, `\PaperAffiliation`, `\CompanionAuthor` and `\RepositoryNote`
at the top of `main.tex` before submission.

## Files

| File | Purpose |
|---|---|
| `main.tex` | The manuscript. |
| `refs.bib` | 43 entries, all cited. |
| `check_paper.py` | Exact replay of every constant printed in the paper (2083 assertions); writes `check_paper_output.json`. |
| `make_figures.py` | Regenerates `figures/population_vs_cycles.pdf` and `figures/minority_loss.pdf`. |
| `build.ps1` | Runs both scripts, then `pdflatex`/`bibtex`/`pdflatex`×2 in a scratch directory, and copies the PDF back. |

## Build

```powershell
.\build.ps1
```

MiKTeX is expected under `%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`
(the script prepends it to `PATH`). The build runs in `%TEMP%` so that a
failed run cannot leave a stale `main.aux` next to the source; the script
asserts `main.aux` exists afterwards and warns on any overfull box or
undefined reference. Expect a clean log: no overfull boxes, no undefined
references or citations.

Two MiKTeX quirks are handled in `build.ps1` and should not be "fixed":
`$ErrorActionPreference` is lowered to `Continue` around the native LaTeX
calls because MiKTeX writes an update nag to stderr, which PowerShell would
otherwise promote to a terminating `NativeCommandError`; and `\lean{}`
(a `\DeclareUrlCommand`) must never appear inside a `\caption`, since `\url`
breaks in a moving argument.

## Evidence classes

The paper labels every nontrivial statement as machine-checked, conventional,
or numerical. Appendix B carries the claim-to-declaration map.

**Machine-checked** (frozen Lean 4.30.0 + Mathlib, publication root
`proofs/SerialTransferSelection/PublicationResolution.lean`, receipt
`problem_workspaces/RAF_state_selection_many_serial_transfers/verification/publication.json`):
Theorem 3.1, Corollary 5.2, Proposition 5.1, Proposition 5.4,
Theorem 6.1 and its terminal composition, Proposition 6.3, Proposition 7.1,
Table 4, and the scalar inequality of Lemma 4.4 (receipt
`verification/minority_barrier.json`, root `MinorityGrowthBarrier.lean`).

**Conventional, written out in full in the paper** — these are new here and
are *not* compiled:

* Proposition 4.1 (multiplicative concentration for weighted uniform sampling
  without replacement, via Hoeffding's convex-comparison theorem plus the
  standard Chernoff optimization);
* Proposition 4.3 (exact finite-population variance);
* Theorem 4.5 (both ancestral size totals grow by a factor ≥ 3/2 during a
  batch): the scalar generator inequality is compiled, the lifting to the batch
  population statement reuses in written form the same barrier/uniformization
  machinery that *is* compiled for the size-odds statement;
* Theorem 4.7 and Theorem 6.2 (refined mission theorem and its witness);
* Corollaries 5.3, 6.4 and Theorem 5.5.

A reader who wants to stay entirely inside the machine-checked perimeter can
use Theorem 3.1, Corollary 5.2 and Theorem 6.1; nothing in Section 4 affects
them.

## The refinement, in one paragraph

The compiled share recurrence loses a factor 4 per cycle because the batch
quadruples the total size while the minority is only known not to shrink, giving
base `R = 204/49`. Theorem 4.5 supplies the missing growth: the nonnegative
observable `V = exp[(N/1000)(η log W − log L)]` with `η = 8/25` is a
supermartingale under the growth jumps (the resident channels and complementary
division leave both ancestral totals fixed), because the compiled ancestral rate
sandwich `2.97 ≤ Z_H/B_H ≤ 3`, `0.99 ≤ Z_L/B_L ≤ 1.01` makes the compiled
scalar inequality applicable pointwise. Since `W` quadruples, a Markov bound
gives `B_L⁻ ≥ (3/2) B_{L,0}` except with probability `exp(−19N/500000)` — a term
already present in the error, because `(8/25)log4 − log(3/2) = 0.0381588… ≥
19/500` with margin `1.49×10⁻⁴`. The high ancestry needs no new barrier: the
compiled gain and persistence give `B_H⁻/B_{H,0} > e^{b⋆} > 3/2` directly. The
base improves to `R⋆ = 136/49` and the sufficient leading coefficient from
`0.701115` to `0.979591`, against a necessary `1/g = 1.326662`.

`η` cannot be pushed past `0.99·0.999/3 = 0.32967` with this barrier — that
ceiling comes straight from the certified sandwich — so closing the rest of the
gap needs a different estimate, not a better constant here.

## Numbers a future editor will want

| | Theorem 6.1 (compiled) | Theorem 6.2 (refined) |
|---|---:|---:|
| `M` | `10¹³` | `4×10⁹` |
| `N` | `6.5536×10²²` | `6.5536×10²²` |
| transfer | `0.003956352374` | `0.000967176369` |
| chemistry | `0.000010842024` | `0.000000004337` |
| service | `0.002` | `0.002` |
| confidence | `≥ 0.994` | `≥ 0.997` (`≥ 0.999` with `s < 10⁻⁶`) |
| `C_L` floor | `1 598 083` | `36 862` |

`g = 0.753771282058…`, `e^g = 2.124998894`, `R = 4.1632653`,
`R⋆ = 2.7755102`, reduced-model diagnostic base `4^{1−z_L/z_H} = 2.515536575`.

Run `check_paper.py` after any numerical edit; it re-derives all of these with
`Fraction` arithmetic and explicit-remainder log/exp enclosures, so a changed
constant fails an assertion rather than silently propagating.
