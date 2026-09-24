# Optimal affinity paper: LaTeX source

`main.tex` is the complete arXiv source of

> *Optimal affinity of autocatalytic networks beyond gross stoichiometry: a counterexample, the response-profile capacity, and its kinetic realization*

The bibliography is inline (`thebibliography`), so no BibTeX run is needed.

## Compile (Windows, MiKTeX user install)

```powershell
& "$env:LOCALAPPDATA\Programs\MiKTeX\miktex\bin\x64\pdflatex.exe" -interaction=nonstopmode main.tex
& "$env:LOCALAPPDATA\Programs\MiKTeX\miktex\bin\x64\pdflatex.exe" -interaction=nonstopmode main.tex
```

Two passes resolve cross-references and the table of contents. The finished PDF is copied to
`..\Optimal_Affinity_Response_Capacity_arxiv.pdf`.

## Notes for future edits

* Packages: `amsart`, `amsmath/amsthm/mathtools`, `booktabs`, `enumitem`, `listings` (Lean snippets, with a
  `literate` table for the Unicode symbols used in Lean), `tikz` (Figure 1), `float` (`[H]` tables), `hyperref`.
  Do not add `cleveref`; it conflicts with `amsart` in this MiKTeX setup.
* Long Lean identifiers in prose are written as `\texttt{name\_\allowbreak part}` so they can break at underscores.
* Section 9.2 lists exactly which steps are hand-checked rather than Lean-verified (rooted/one-terminal-class
  equivalence, the primitive form of the class, the rescaling remark, the general-`d` power sources, the
  detailed-balance states). Keep that list in sync with any changes to the mathematics.
* Author/affiliation/acknowledgement fields are placeholders to be filled in before submission.

## Provenance

Source material: `problem_workspaces/RAF_optimal_affinity_conjecture`,
`problem_workspaces/RAF_optimal_affinity_corrected_theory`, `problem_workspaces/RAF_optimal_affinity_source_closure`,
`problem_workspaces/RAF_kinetic_realizability_optimal_affinity_response_profile`, and the Lean libraries
`proofs/OptimalAffinity`, `proofs/OptimalAffinityCorrected`, `proofs/OptimalAffinityRealizability`,
`proofs/ThermoCoreCompatibility`.
