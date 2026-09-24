# Reproduction and evidence map

Run from `E:\Erdos Problems` using the frozen repository environment. No package installation, dependency update or generated-evidence commit is required.

```powershell
.\.venv\Scripts\python.exe scripts/check_python.py --quiet
.\.venv\Scripts\python.exe scripts/smoke_numerics.py
.\.venv\Scripts\python.exe scripts/process_guard.py run --timeout 120 --owner-label TW-PILOT -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_cancer_therapeutic_windows_disrupting_cellular_memory/experiments/pilot.py
.\.venv\Scripts\python.exe scripts/process_guard.py run --timeout 120 --owner-label TW-REFINE -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_cancer_therapeutic_windows_disrupting_cellular_memory/experiments/refine.py
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/TherapeuticWindows/Root.lean --timeout 180 --declaration TherapeuticWindows.finite_therapeutic_window_certificate --output problem_workspaces/RAF_cancer_therapeutic_windows_disrupting_cellular_memory/verification/root.json
```

The numerical scripts limit BLAS/OpenMP threading to one, have six target states and at most 21 healthy states, and took approximately two seconds each on this run. The guarded 120-second limit is conservative. The verifier enforces `mathlib4_project/` as its working directory, the pinned toolchain, warning-as-error, and local dependency materialization. Cached successful dependencies are reused only through that bridge. The broad Mathlib import was replaced with focused imports to reduce loading cost.

Do not rerun `bootstrap.py`: it is the one-time initializer and would reset the local ledger. The two experiment scripts are the minimal source/checking package and do not import the predecessor workspace. Their source reconstruction is self-contained. Their reproduction of prior constants does not reverify the predecessor's complete proofs.

| Claim | Evidence | Kind |
|---|---|---|
| Literal source, no extra dilution, Jacobian sign | pilot.py `source`, `exact`; Source.lean `source_linearization`, `source_mass` | E,K plus interpretation C |
| Old barrier and schedule reproduction | pilot.json `exact`, `source_schedule_reproduction` | E,N respectively |
| Source weight contraction on a real interval | Source.lean `source_contraction`, `source_ramp_growth` | K |
| All-policy selected-lineage exclusion | THEORY.md section 2; Clock.lean `clock_two`, `exclusion_certificate`; Source.lean `source_hazard_domination` | C with K finite inequalities |
| Logistic cap and healthy numerical margin | Reserve.lean `logistic_cap`, `ten_step_excursion_product`, `reserve_certificate` | K |
| General excursion upper/lower laws and buffer dichotomy | THEORY.md section 3 | C, not stochastic K |
| Complete delivered course and probability bounds | THEORY.md section 4; ROOT_CONTRACT.md | C |
| Explicit parameter-box envelope | Robustness.lean `perturbation_budget`; refinement.json exact | K,E |
| Delivery and exponential Taylor certificates | Delivery.lean `delivered_course_arithmetic`, `exponential_lower_certificates` | K |
| Modular assembled finite statement | Root.lean `finite_therapeutic_window_certificate`; verification/root.json | K when `verified=true` |
| Matched schedules, healthy path/endpoint distinction | pilot.json | N |
| Sister-kernel boundary shift, power-law pilot | refinement.json | N |
| Erasure sign counterexample | refinement.json `exact_preparation_coefficients`; THEORY.md section 5 | E,C |
| Progress, failed routes and decisions | campaign/TASKS.md, campaign/HYPOTHESIS_GRAPH.md, campaign/daily/2026-09-21.md | Local research records |

The final root is a conjunction of actual finite source inequalities, exact excluded/feasible margins, and perturbation/exponential certificates. It does not take the desired stochastic feasibility statement as an assumption. It also does not purport to prove that statement in Lean: the controlled-process construction, time-change coupling, strong Markov excursion argument, and expectation-to-event steps remain conventional proofs in THEORY.md.

AGC reproduction:

```powershell
.\.venv\Scripts\python.exe scripts/agc.py checkpoint problem_workspaces/RAF_cancer_therapeutic_windows_disrupting_cellular_memory
```

This currently returns `AGC-LAUNCH-E005` because no authoritative specification exists. The actual diagnostics are retained in `verification/agc_*.txt`; no current-authority status is claimed. An authorized future integrator may supply the real specification and dock the evidence, but that publication is not mathematical proof and is not required to replay these local results.
