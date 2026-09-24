# Minimal reproduction from the repository root

Use the locked Python 3.11 interpreter; no package or Lean dependency updates.
Exact binary inputs must be real NPZ files, not Git LFS pointers. The source
can also be reconstructed from finite_source_exact.json. Hashes of inputs,
checkers and saved receipts are in postproof_input_hashes.json; hashes are
provenance, not proof.

```powershell
& '.\.venv\Scripts\python.exe' scripts/check_python.py --quiet
& '.\.venv\Scripts\python.exe' scripts/smoke_numerics.py
& '.\.venv\Scripts\python.exe' scripts/agc.py checkpoint problem_workspaces/RAF_switchable_phosphorylation_clock --format json
& '.\.venv\Scripts\python.exe' scripts/process_guard.py run --timeout 600 --owner-label CLOCK-replay -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_switchable_phosphorylation_clock/replay.py
& '.\.venv\Scripts\python.exe' problem_workspaces/RAF_switchable_phosphorylation_clock/single_input_rank_certificate.py
& '.\.venv\Scripts\python.exe' problem_workspaces/RAF_switchable_phosphorylation_clock/sink_capture_certificate.py
& '.\.venv\Scripts\python.exe' scripts/verify_proof.py proofs/SwitchablePhosphorylation/SingleInputColumn.lean --output problem_workspaces/RAF_switchable_phosphorylation_clock/single_input.verify.json
& '.\.venv\Scripts\python.exe' scripts/verify_proof.py proofs/SwitchablePhosphorylation/CaptureInequality.lean --output problem_workspaces/RAF_switchable_phosphorylation_clock/capture.verify.json
```

The full replay costs about 90 seconds on the observed machine. Lean imports
took several minutes under concurrent machine load; the saved strict receipts
can be inspected without rebuilding unchanged modules. The proof bridge sets
the correct pinned mathlib working directory and treats warnings as errors.

The following are optional numerical investigations, not theorem checkers:

```powershell
& '.\.venv\Scripts\python.exe' scripts/process_guard.py run --timeout 150 --owner-label CLOCK-pilot -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_switchable_phosphorylation_clock/scalar_control_pilot.py --optimize --periods 3 --phase 1.5707963267948966
& '.\.venv\Scripts\python.exe' scripts/process_guard.py run --timeout 100 --owner-label CLOCK-basin -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_switchable_phosphorylation_clock/basin_followup.py
& '.\.venv\Scripts\python.exe' scripts/process_guard.py run --timeout 90 --owner-label CLOCK-Hessian -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_switchable_phosphorylation_clock/capture_neighborhood_pilot.py
& '.\.venv\Scripts\python.exe' scripts/process_guard.py run --timeout 180 --owner-label CLOCK-physical -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_switchable_phosphorylation_clock/physical_followup.py
& '.\.venv\Scripts\python.exe' scripts/process_guard.py run --timeout 100 --owner-label CLOCK-noise -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_switchable_phosphorylation_clock/physical_interpretation.py
```

For the paper, use the checked-in editable publication/paper.tex,
publication/exact_tables.tex and publication/waveform_vector.pdf. Run
pdflatex twice with publication/ as the working directory, then copy paper.pdf
to Switchable_Phosphorylation_Clock.pdf in the project root. The one-time
revise_publication.py migration is historical, not an idempotent build step.
The final manuscript intentionally omits discovery-only plots and the
superseded full-actuation lemma. The mathematical supplement stands alone;
the broader physical and failed-control investigations remain research records.
