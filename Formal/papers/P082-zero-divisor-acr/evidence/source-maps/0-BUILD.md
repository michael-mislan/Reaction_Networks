# Build and provenance

Paper: *Zero-divisor methods for absolute concentration robustness: completeness,
positive geometry, and quantitative certificates* (20 September 2026, 24 pages).
Author/affiliation macros at the top of `main.tex` are blank on purpose
(`\PaperAuthor`, `\PaperAffiliation`, `\PaperDate`). The PDF metadata has title,
subject and keywords; add `pdfauthor` in `\hypersetup` when the author is set.

## Files

| File | Role |
|---|---|
| `main.tex` | Manuscript (Figure 1 is inline TikZ) |
| `refs.bib` | Bibliography (superset; only cited entries print) |
| `main.bbl` | Generated bibliography; include in an arXiv upload |
| `make_figures.py` | Writes `figures/reactor_envelope.pdf`, `release_costs.pdf`, `ellipsoid.pdf` |
| `check_paper.py` | Replays every printed identity and number exactly (SymPy); must end in `"status": "PASS"` (74 checks) |
| `anc/lean/` | Copy of `proofs/ACRZeroDivisors/*.lean` (41 modules) for arXiv ancillary files |
| `anc/README.md` | Toolchain, roots, axioms, receipts |

## Commands (MiKTeX, user scope; Git Bash)

```bash
export PATH="$LOCALAPPDATA/Programs/MiKTeX/miktex/bin/x64:$PATH"
PY="/e/Erdos Problems/.venv/Scripts/python.exe"
"$PY" make_figures.py        # matplotlib, numpy, scipy
"$PY" check_paper.py         # sympy
pdflatex --disable-installer -interaction=nonstopmode main.tex
bibtex main
pdflatex --disable-installer -interaction=nonstopmode main.tex
pdflatex --disable-installer -interaction=nonstopmode main.tex
```

After building, check `main.log` for `^!`, `Warning`, `Overfull`, `Underfull`,
`undefined` (last build: none; the MiKTeX "check for updates" nag on stderr is
environmental). The final PDF is copied to
`key_results/RAFs/Zero_Divisor_Methods_Absolute_Concentration_Robustness.pdf`.

For arXiv: upload `main.tex`, `main.bbl`, `figures/*.pdf` and `anc/`. The PDF
abstract is about 2200 characters; arXiv's metadata field allows 1920. A
plain-text version within the limit is at the end of this file.

New Lean module (compiled 2026-09-20, strict, axioms `propext`,
`Classical.choice`, `Quot.sound` only):

```powershell
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/ACRZeroDivisors/RegularityCertificates.lean --declaration ACRZeroDivisors.envZ_regular_minor --output problem_workspaces/RAF_ACR_questions_4o7_3o11/verification/regularity_certificates.verify.json
```

## Sources

* Workspace `problem_workspaces/RAF_ACR_questions_4o7_3o11` (16-page draft
  `ACR_Research_Paper.tex`, `paper/PAPER_SUPPLEMENT.md`, `PAPER_HANDOFF_REPORT.md`,
  `experiments/extension_exact.py`).
* Plan: `ACR_Supplemental_Information_and_Publication_Guidance_2026-09-20.md`.
* Lean: `proofs/ACRZeroDivisors/*.lean`; receipts in the workspace `verification/`.
* Source statements (Question 3.13, condition (13), the definition of elimination
  order in Section 4.1, Definition 4.2, Algorithm 1, Conjecture 4.7, Lemma 4.14,
  Examples 3.11, 3.12, 3.15) were re-read from the arXiv v3 PDF of
  Garcia Puente et al. on 2026-09-20. arXiv:2412.17798 is now v3 (14 May 2026,
  accepted in SIAGA); its Theorem B is still "Theorem 4.4, Corollary 4.7".
  All DOIs in `refs.bib` except Weispfenning 1992 and the two books without DOI
  were checked against Crossref on 2026-09-20.

## What changed relative to the 16-page draft

* **Theorem 6.2 (regular-point coverage) has a new proof and a stronger
  statement.** The draft went through complexification, Zariski density and a
  descent of a conjugation-invariant prime. The new proof is entirely real:
  the local ring of the original ideal at a regular point is a regular local
  ring (Matsumura 14.2/14.3), hence a domain; the analytic implicit function
  theorem plus Krull's intersection theorem put `x_i - alpha` in the unique
  minimal prime through the point. New conclusions: the multiplier `h` can be
  chosen with `h(x*) != 0` (so a regular point is locally well conditioned,
  linking Sections 6 and 7), and only *local* constancy near `x*` is needed,
  so local ACR values are covered too.
* **Notation:** `n` species, `s` stoichiometric rank everywhere; the hypothesis
  is stated as `rank Df(x*) = s`.
* **Source accuracy:** the definition of elimination order, Algorithm 1 (reduced
  basis; univariate branch vs. leading-coefficient branch) and Definition 4.2
  are now stated as in the source; Corollary 5.2 separates the two branches.
* **New Remark 4.2:** under the mixed order the rephrased Suzuki-Sato lemma
  ([acr, Lemma 4.14]) also fails at `alpha = 2` (specialised set is not a
  Groebner basis of `<u,v>`); replayed in `check_paper.py`. No claim is made
  about the original Suzuki-Sato hypotheses.
* **New Example 6.7:** EnvZ/OmpR minor `-k1 k4 k6 k7 k9 x2 x4`; every positive
  steady state is regular, `s = 5`. Lean: `envZ_regular_minor`.
* **New Proposition 8.4:** explicit invariant ellipsoid `V <= 1/5` with rational
  Lyapunov matrix. The supplement's norm-based version gave `r0 ~ 0.0255` and an
  inscribed ball of radius 0.0036 uM; bounding the cubic term through its factor
  `u_a` and the `P`-weighted coordinate bounds gives `b >= 1.573`, inscribed
  ball 0.045 uM (about 12x larger). Lean: `reactor_lyapunov`,
  `reactor_lyapunov_minors`, `reactor_P_inverse`, `reactor_cubic_form`,
  `reactor_ellipsoid_constants`.
* Boundedness of reactor solutions, Proposition 8.3 (time average) stated with
  its hypotheses, remark separating regularity from deficiency / multistationarity
  / class-restricted degeneracy, certification sequence, result map (Table 1),
  formal-scope table (Table 2), introduction, related work and 25 references.
* Explicit ideal-membership witnesses were added to Propositions 3.1 and 3.2.

## arXiv metadata abstract (plain text, under 1920 characters)

A mass-action system has absolute concentration robustness (ACR) in a species
whose concentration is the same at every positive steady state. Garcia Puente et
al. proposed to detect ACR values as the positive numbers alpha for which
x_i - alpha lies in, or is a zero divisor of, the steady-state ideal, and to list
them from leading coefficients of a Groebner basis. We settle two questions they
left open. For networks with at most bimolecular complexes, uniqueness of such a
value is neither necessary nor sufficient for ACR. Their candidate algorithm is
incomplete for an elimination order that their definition admits, and we prove
that it is complete for block orders. We show that one positive steady state at
which the Jacobian has rank equal to the stoichiometric rank forces every ACR
value, global or local, to be a zero-divisor value, with a multiplier that does
not vanish there. We then make such identities quantitative: a lower bound on the
multiplier converts an identity into a bound on |x_i - alpha| in terms of
residuals and signed load terms. For a loaded reactor we obtain the exact
positive operating region, a smaller conditioning region, local stability, and
an explicit rational Lyapunov ellipsoid on which the bound holds for all time.
For the EnvZ/OmpR model every positive steady state is regular and steady states
are classified by total amounts. Replacing a reaction with more than two product
molecules by a chain of private intermediates preserves the steady-state
quotient ring and all ACR values, while adding explicit residual, storage and
leakage terms. The algebraic results are compiled in Lean 4 with Mathlib;
geometric and dynamical arguments are conventional proofs.
