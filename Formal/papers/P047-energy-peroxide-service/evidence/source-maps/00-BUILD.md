# Build and provenance notes

**Paper.** *Energy service and peroxide handling in a proteome-constrained
red-cell model: exact inventory certificates, a certified turnover plateau, and
kinetic limits.* 21 pages, author and affiliation deliberately blank
(`\PaperAuthor`, `\PaperAffiliation` at the top of `main.tex`).

## Files

| File | Role |
|---|---|
| `main.tex` | The manuscript. Single file, no included sections. |
| `refs.bib` | 16 references. Every entry's author list, volume, issue, pages and year was checked against Crossref during preparation; several author names in the earlier draft were wrong and were corrected. |
| `figures.py` | Generates `figures/fig1.pdf`, `fig2.pdf`, `fig3.pdf` from numbers copied out of the saved repository records. No solver is run. |
| `check_paper.py` | Replays every number printed in the manuscript against the saved records and the Lean receipts. 84 checks; must print `0 failed`. |
| `build.ps1` | Runs the checks, regenerates the figures, then builds with MiKTeX in a scratch directory and copies the PDF back. |
| `main.pdf`, `main.bbl`, `main.log` | Build outputs, kept for convenience. |

Build with

```powershell
powershell -ExecutionPolicy Bypass -File build.ps1
```

MiKTeX is user-scope and not on `PATH`; `build.ps1` prepends
`%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`. **The C: drive on this machine
is full**, so the build scratch directory is placed under `E:\tmp`. For the same
reason, set `TMPDIR=/e/tmp` before running anything through a POSIX shell here.

For an arXiv submission upload `main.tex`, `refs.bib` (or `main.bbl`) and
`figures/*.pdf`. `figures.py`, `check_paper.py` and `build.ps1` are authoring
aids and need not be submitted.

## Evidence classes, stated exactly as the paper states them

| Result | Evidence |
|---|---|
| Theorem 3.1, the full-source inventory bound | Lean 4. `StoredRedCells.S7Certificate.source_joint_inventory_bound` in `proofs/StoredRedCells/S7Source.lean`; receipt `problem_workspaces/Medical_red_blood_cells_.../s7_source.verify.json`. |
| Lemma 5.1, Propositions 5.2, 5.3 | Lean 4. `PlateauEnclosure.{feasible_nonempty, uniform_enclosure, value_antitone, value_concave, infeasible_above_ceiling}`. |
| Theorem 7.1, the sharp transient carrier bound | Lean 4 for the inequality (`PlateauEnclosure.carrier_transient_bound`), conventional for the sharpness claim and Corollary 7.2. |
| Recovery identity, discrepancy bound, logarithmic interval (Section 8) | Lean 4. `PairedRecovery.{normalized_integrated_identity, paired_robustness, observation_rate_interval}`. |
| Theorem 5.4, the plateau instance | Exact rational primal/dual audit in Python. **Not** a Lean-replayed source certificate. |
| Sections 4 and 6, sensitivities, cleanup, media table | Floating-point linear programs; feasibility of a relaxation only. |

`proofs/StoredRedCells/PlateauEnclosure.lean` was written for this paper. It
verifies in one strict compilation (Lean 4.30.0, warnings as errors, no `sorry`,
axioms `Classical.choice`, `Quot.sound`, `propext` only; 42.4 s), receipt
`proofs/StoredRedCells/PlateauEnclosure.verify.json`. Two hypothesis sets in it
are declared but inert, and the paper says so in the appendix: `0 <= m_h` in the
enclosure lemma, and the rate nonnegativity `0 <= v`, `0 <= u` in the carrier
bound. The compiled carrier statement also drops `0 <= g <= C` (never needed)
while strengthening the differentiability hypothesis relative to the paper's
almost-everywhere version.

## What is new here relative to the earlier draft

1. **The certified service interval was extended from `m <= 1.02417` to
   `m <= 1.0345238`**, and an exact rational *service ceiling*
   `M <= 1.0345238944791832` was certified for the same polytope. Together these
   cover 99.99999% of the attainable service range instead of 98.9992% of a
   floating-point maximum, and they turn the plateau statement into a
   description of the whole question rather than of a sub-interval. New scripts:
   `plateau_extend.py` (discovery) and `certify_plateau_full.py` (exact audit),
   both in the problem workspace; new record `plateau_full_audit.json`. The
   earlier `plateau_exact_audit.json` is retained and is referenced in the paper
   as superseded.
2. **Theorem 7.1** replaces the draft's harmonic bound, which required a
   terminal balance, by a sharp bound with no terminal condition, together with
   its attainment, the `O(1/T)` approach to the harmonic ceiling, the quadratic
   start from a fully oxidised pool, and the inverted carrier requirement.
3. **Lemma 5.1 and Propositions 5.2, 5.3** state and prove the one-witness
   principle, concavity and the ceiling argument that were implicit before.
4. All of 1--3 are Lean-verified except the plateau instance itself.

## Pitfalls hit while building this package (all fixed)

- `\Nc_{,j}` where `\Nc` already ends in a subscript gives *Double subscript*.
  Write `N_{\mathrm c,j}` instead.
- A `\DeclareUrlCommand` macro such as `\lean{...}` inside a `\caption{}` fails
  with *`\url` used in a moving argument*. Use `\texttt{}` in captions.
- 64-character digests have no break points and overflow the margin. They are
  typeset with `\hashfour{}{}{}{}`, four 16-character pieces joined by
  `\allowbreak`. `check_paper.py` flattens that macro before matching.
- `\textsc` inside an italic theorem statement requests the missing shape
  `T1/lmr/m/scit`; `\rx` wraps it in `\textnormal`.
- Patching `.tex` or `.py` through a shell heredoc silently eats backslashes
  here. Use the file-writing tools instead.
