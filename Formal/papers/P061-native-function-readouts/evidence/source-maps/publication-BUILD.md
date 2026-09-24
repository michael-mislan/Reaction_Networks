# Biochemical readouts that preserve native function — arXiv source package

Manuscript: *Biochemical readouts that preserve native function: reporter
storage, finite-time inference and certified recovery in a shared cofactor
pool*, 17 September 2026, 24 pages, 4 figures (one inline TikZ), 6 tables,
14 references. The author and affiliation macros (`\PaperAuthor`,
`\PaperAffiliation` at the top of `main.tex`) are intentionally empty.

Built PDF: `../Biochemical_Readouts_Native_Function.pdf` (identical to
`main.pdf` here).

This article supersedes the eight-page workspace report in
`problem_workspaces/RAF_Assays_biochemical_readouts_function_preservation/`
(`paper.tex`). It keeps that paper's source, its exact operating region and its
numerical comparison, and adds the results developed for this release.

| Addition | Where | Status |
|---|---|---|
| Complete-recovery cost is a **schedule invariant** (any nonnegative association profile of finite total exposure), with convergence proved rather than assumed | Thm 3.3 | conventional; the algebra is Lean |
| General **design criterion** stated before the rational witness | Thm 4.4 | conventional |
| Absolute (not merely relative) preservation envelopes `e < 0.032`, `b < 0.0028` | Thm 5.1 | newly Lean-verified |
| Remainder identity carrying the **residual association mass** `V` | Prop 6.1 | newly Lean-verified |
| **Fading-switch** recovery theorem: `α(T+s) ≤ α₀e^{-γs}` replaces `α = 0` | Thm 6.4 | conventional; certificates Lean |
| Certified **recovery deadline as a function of γ** (table + figure) | Tab 3, Fig 2 | exact rational arithmetic |
| Additional complete loss under a fading switch is bounded **and nonzero** | Prop 6.6 | newly Lean-verified at γ = 21 |
| **Continuous bounded-error outer sets** for `p` and for the native flux | Prop 7.1, Fig 3 | inversion newly Lean-verified |
| **Divided-slope sandwich** for nonlinear native/regeneration kinetics, with the Michaelis–Menten low-saturation limit | Thm 8.1, Ex 8.2 | newly Lean-verified |
| Real-exponential recovery certificates (not just rational arithmetic) | Thm 6.2, Cor 6.5 | newly Lean-verified |

Two substantive corrections relative to the earlier workspace draft and its
supplemental report:

* The draft used the *relative* suppression bound `0.0473` as if it were an
  absolute bound on `e(T)`. The absolute bound is `49306887/1544000000 <
  0.032`, and the complex bound is `111807/40000000 < 0.0028`; using the correct
  absolute constants tightens the ideal-switch remainder from `2.5e-6` to
  `1.21e-6`.
* The supplemental report's fading-switch corollary asserted `τ = 5` at
  `γ ≥ 21` with a constant `B* = 0.0598` whose derivation is only valid if the
  exponential kernel is dominated *before* the convolution is bounded. That step
  is now stated explicitly as Lemma 6.3, and the corollary is re-derived with
  admissible certified rates `(ν₀, ν₁) = (1.93, 12)`.

## Files

| File | Role |
|---|---|
| `main.tex` | manuscript source (11pt article, natbib numbers, `plainnat`) |
| `references.bib` | all 14 references, each field confirmed against Crossref/publisher records |
| `recovery_rows.tex` | generated; macro `\recoveryrows` holding the six rows of Table 3 |
| `comparison_rows.tex` | generated; macro `\comparisonrows` holding the three rows of Table 4 |
| `figures/design.pdf` | Figure 4: certified signal margin and numerical suppression |
| `figures/deadline.pdf` | Figure 2: certified recovery time against switch decay rate |
| `figures/inference.pdf` | Figure 3: outer sets for `p` and for the native flux |
| `check_paper.py` | recomputes every printed constant and regenerates all figures |
| `results.json` | generated; exact rationals and numerical values |
| `main.bbl` | generated; include it in an arXiv upload alongside `references.bib` |
| `lean/*.lean` | the two proof modules, copied verbatim from `proofs/` |
| `verification/*.verify.json` | strict verification receipts (command, hashes, axioms, elaborated statements) |

Figure 1 is inline TikZ; there is no external file for it.

## Rebuild

From this directory, with the repository Python and MiKTeX on `PATH`
(`%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`):

```bash
python check_paper.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

`check_paper.py` runs 90 assertions and exits non-zero on any failure. A clean
build has no `!` lines, no overfull/underfull boxes and no undefined references
in `main.log`; check that, because a full disk makes pdflatex silently drop
`main.aux` and ship a PDF full of `??` references.

## Lean verification

Environment: Lean 4.30.0, repository-pinned Mathlib
(manifest SHA-256 `a8df0b606ec258561c226df89856884be433c19b49fb0a27335d69bb2b6e9fac`),
strict compilation with `-DwarningAsError=true`. No `sorry`; every exported
declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

```powershell
$ResearchPy = Join-Path 'E:\Erdos Problems' '.venv/Scripts/python.exe'
& $ResearchPy scripts/verify_proof.py proofs/BiochemicalReadout.lean `
    --timeout 900 --declaration BiochemicalReadout.joint_protocol
& $ResearchPy scripts/verify_proof.py proofs/BiochemicalReadoutExtensions.lean `
    --timeout 900 --declaration BiochemicalReadout.Ext.fading_recovery_tail
```

| Module | SHA-256 | Verified | Roots probed |
|---|---|---|---|
| `BiochemicalReadout.lean` | `6b72e6f54b3f229973b3359b3ca8f08f16173b74ed0cbeca702dd3f14d24a504` | true, 25.0 s | `joint_protocol`, `finite_account`, `turnover_cost` |
| `BiochemicalReadoutExtensions.lean` | `16015cde419dc8dc07464d2e8d975c94ff4a91014cd0f627ed730c7b880f052b` | true, 27.7 s | `fading_recovery_tail`, `ideal_recovery_tail`, `slope_sandwich` |

### What is compiled and what is not

Compiled: the literal field subtraction and the stored-deficit equation; the
finite integral account from its derivative premise via the fundamental theorem
of calculus; the cost-coefficient rearrangement; both forms of the
outstanding-loss functional, including the form carrying the residual
association mass; the divided-slope sandwich (stated division-free, so it needs
neither `I > 0` nor `W ≥ 0`); the Taylor lower bound `exp(9.65) > 14000` and the
resulting bound on `exp(-9.65)`; the ideal-switch and fading-switch recovery
certificates, stated about `Real.exp` rather than about rational surrogates; the
additional complete-loss bound at `γ = 21`; the absolute preservation envelopes;
the class-flux separation; the set-inversion endpoints and the monotonicity of
the stationary flux in `p`; the loading, free-pool and classifier arithmetic;
the alias source equality and its error-sum arithmetic.

Conventional (proved in the paper, not in Lean): forward invariance and global
existence; the convergence `b, e → 0` and the integrability that make the
schedule-invariance theorem's limits exist; every scalar comparison argument
behind the preservation and signal envelopes; the two-rate convolution lemma and
the deadline table; the Michaelis–Menten slope ranges and the low-saturation
limit; the uniqueness step in the alias argument. Every biochemical mapping is a
premise, not a result.

Table 6 of the paper states this split; keep the two levels distinct when
citing. A compiled inequality does not validate a biological interpretation, and
a conventional proof is not thereby weaker.

## Numerical checks

`check_paper.py` verifies, among 90 assertions:

* every exact rational constant in the paper and in Appendix A, including
  `U(8)`, `L(8)`, the separation `1214759671/218587500000` and the threshold;
* that the *rounded* envelopes printed in Theorem 5.1 are dominated by the
  sharp ones of Theorem 4.4, in the correct direction on each side;
* the acquisition-time boundary of the printed certificate (negative margin at
  `T = 6`, positive at `T = 7`);
* each row of the recovery-deadline table, and that the same test fails at
  `τ - 0.1`, so the tabulated deadlines are tight to one decimal place for this
  bound;
* sixteen reproducible interior draws (seed `17092026`) against the proved
  suppression bound and the proved recovery remainder, with maximum accounting
  residual `1.1e-12`;
* schedule invariance of `D_∞/q_∞` across four schedules, to `1e-12`;
* that the slow/fast complete-loss ratio `1.787` equals `(2/1.05)` rescaled by
  the realised complete products `0.28830` and `0.30731`;
* the fading-switch extra complete losses `0.00096`, `0.00405`, `0.02041` at
  `γ = 21, 5, 1` against Proposition 6.6;
* the nonlinear cost ratio `0.523612` from a direct integration of the
  saturating source, inside the proved sandwich `[0.43388, 0.63]`;
* the compatible record range `[0.2650, 0.4661]` for the continuous contract.

## Pitfalls hit while building this package

* The Lean `unusedVariables` linter is an *error* under `-DwarningAsError=true`.
  Three hypotheses (`0 < I` and `0 ≤ W` in `slope_sandwich`, `0 ≤ y` in the two
  inversion lemmas) turned out to be genuinely unnecessary and were removed
  rather than silenced, which strengthens the statements.
* In this Mathlib revision the division lemmas carry the `₀` suffix:
  `div_lt_div_iff₀`, `div_le_iff₀`, `le_div_iff₀`, `div_le_div_iff₀`. The
  unsuffixed names no longer resolve.
* Long Lean identifiers overflow the `tabularx` evidence table; redefining
  `\leanref` to insert `\allowbreak` after each escaped underscore fixes it
  without hyphenating identifiers.
* Two displays (`U(T)`/`L(T)` and `A_L`/`A_U`) are too wide side by side and
  need `aligned` or a second display.
* Bash heredocs in this environment eat backslashes, so LaTeX and Lean patch
  scripts must be written to a file rather than piped in.
