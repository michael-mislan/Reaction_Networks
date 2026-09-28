# Build notes: A critical-point criterion for D-stability in every dimension

Title: *A critical-point criterion for D-stability in every dimension* (shortened on 2026-09-28 from "Critical points on Johnson's contact variety: a
machine-checked D-stability criterion, an explicit 5×5 critical-point system, and time-scale robustness margins").

This is the arXiv-ready source (September 2026, referee-revised) for phase 2 of the T-5×5 campaign
(`problem_workspaces/D_stability_5x5_characterization/`). The PDF is copied to
`problem_workspaces/D_stability_5x5_characterization/D_Stability_Contact_Critical_Points.pdf` and
`key_results/RAFs/D_Stability_Contact_Critical_Points.pdf`. The referee report and the point-by-point response are
in `qa/`.

## Pipeline (run from the repository root with the repository interpreter)

1. **Evidence.** Experiments in the workspace (`experiments/*.py`), with outputs in `experiments/out/`. Jobs longer
   than 30 s run under `scripts/process_guard.py`.
2. **Validation text.** `problem_workspaces/D_stability_5x5_characterization/experiments/make_validation.py` writes
   `validation.tex`. Set `PYTHONIOENCODING=utf-8` on Windows consoles.
3. **Tables and macros.** `make_results.py` writes `results.tex` and the table fragments `*_table.tex` from the
   evidence.
4. **Figures.** `make_figures.py` writes `figures/fig_*.pdf` (vector).
5. **Replay.** `check_paper.py [--full]` replays every printed number and writes `check_results.json`. It also:
   - regenerates all fragments and compares them;
   - re-verifies all 541 atlas certificates;
   - checks that every `\lean{}` name in Table 8 is exported by the verified Paper.lean receipt.

   Then run `make_results.py` again so that `\CheckCount` is current.
6. **Ancillary files.** `make_anc.py` assembles `anc/`: the Lean closure checked against the receipt hashes, a
   path-free receipt, and the decision tool.
7. **LaTeX** (MiKTeX, TEMP/TMP/TMPDIR on E:):

       pdflatex main && bibtex main && pdflatex main && pdflatex main

   Then assert that `main.log` has no errors, no undefined references and no overfull boxes.

## Critical path and its formal status

| Paper statement | Status | Lean declaration (namespace `DStability5x5`) |
|---|---|---|
| Lemma 2.2 (principal-minor expansion) | Lean | `contactDet_expansion`, `pminor_eq_minorR` |
| Lemma 2.3 (Johnson's criterion) | Lean | `dStable_iff_no_contact` |
| Theorem 3.2 (coverage) | Lean | `dStable_iff_morseFor`, `dStable_iff_morse_logBarrier` |
| Theorem 3.4, Corollary 3.5, Theorem 3.6 (the 5×5 criterion) | Lean | `dStable_iff_explicit`, `dStable_iff_lagrange_tangency`, `dStable_iff_five` |
| Lemma 4.2, Theorem 4.3, Corollary 4.4, Theorem 4.5 (boundary dichotomy) | Lean | `not_surjective_iff_tangency`, `regular_iff_rank`, `exists_contact_near_of_regular`, `not_dStable_near_of_regular`, `not_regular_of_mem_closure`, `isOpen_hurwitz_regularContact`, `hurwitz_regularContact_open_not_dStable`, `closure_dichotomy` |
| Theorem 6.2, Proposition 6.3(a), Theorem 6.4 | Lean | `kStable_iff_no_cone_contact`, `kStable_iff_no_boxFaceCritical`, `dStable_iff_forall_kStable`, `kStable_mono`, `exists_least_unstable_ratio`, `eventually_kStable_of_no_contact`, `contact_of_tendsto_not_kStable` |
| Table 4 (diagonal Lyapunov ⇒ D-stable; Al-Doura) | Lean | `dStable_of_diagLyapunov`, `alDoura_dStable` |
| Example 4.6 (B₃: branch (c) cannot be dropped), Proposition 5.1, Proposition 7.1, Example 6.7, n = 3 run | exact | replayed by `check_paper.py` |
| Lemma 4.8, Proposition 6.3(b), Proposition 6.5 | conventional | not formalized (see below) |
| Proposition 5.2, Remark 6.6 | sketch | not formalized |
| Tables 2–7, Figures 2–4, §8 | numerical / exact certificates | replayed by `check_paper.py` from the evidence |

Receipt: `problem_workspaces/D_stability_5x5_characterization/evidence/lean/lean_receipt_Paper.json`.
- Root `proofs/DStability5x5/Paper.lean`; 25 declarations; 47-module import closure.
- Axioms propext / Classical.choice / Quot.sound only.
- Compiled with warnings as errors, without sorry.

The unformalized statements need Mathlib infrastructure that does not exist:
- algebraic generic smoothness;
- multihomogeneous Bézout bounds;
- dimension theory of singular loci;
- certified real-root isolation.

None of them is used by a Lean-labelled statement.
