# Reproduce the proved claims

From `E:\Erdos Problems`, run:

```powershell
.\.venv\Scripts\python.exe scripts/check_python.py --quiet
.\.venv\Scripts\python.exe scripts/smoke_numerics.py
.\.venv\Scripts\python.exe scripts/process_guard.py run --timeout 600 --owner-label CLOCK-replay -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_switchable_phosphorylation_clock/replay.py
```

This replays the local exact root, quintic and spectral/unfolding signs;
directed finite-source Fourier defect; finite/infinite Fourier contraction;
finite positivity/sink/readout; Taylor/QR transverse attraction; and the exact
positive-flux steering algebra. Expect a few minutes on the current machine.
Large numerical kernels are limited to one BLAS thread. Discovery searches,
failed routes, sensitivity probes and figure production are not prerequisites.

The finite witness is defined by the exact dyadic `xstar`, `currents`, `r`
and scales in `fourier_N40.npz`; all other ratios are exactly 1/100. The local
generalized-Hopf patch uses exact decimal rationals in `rational_patch.json`.
The two witnesses are different and must not be mixed. The replay generates
the inverse and checking outputs from these saved source-bound inputs.

The selected Lean algebra can be independently recompiled with:

```powershell
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/SwitchablePhosphorylation/SourceControlAlgebra.lean --timeout 180 --output problem_workspaces/RAF_switchable_phosphorylation_clock/source_control.verify.json
```

The bridge uses the pinned `mathlib4_project` directory and treats warnings as
errors. No `lake update` is required. The replay checks that the already-saved
strict receipt matches the current Lean source. The full dynamical and
switching theorems remain conventional plus validated computation.

The editable manuscript is `publication/paper.tex`, with PNG figures generated
by `scaling_and_figures.py`. Run `pdflatex -interaction=nonstopmode -halt-on-error
paper.tex` twice from `publication/` to rebuild it. The supplement is editable
Markdown. The final handoff and daily ledger distinguish proofs, numerical
diagnostics and remaining narrower questions.
