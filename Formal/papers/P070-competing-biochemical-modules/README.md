# Compatibility of competing biochemical modules: capacity, recovery, and finite operation

[Read the paper](../../../Applications/Metabolic-and-Redox-Function/P070-competing-biochemical-modules.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

An explicit shared-NADPH model separates stationary compatibility, recovery time and finite operating duration, proving nominal recovery and resource accounts while identifying limits of stationary information.

**Reproduction:** From `manuscript/`, run pdflatex main.tex, bibtex main, then two further pdflatex passes. The archived build.sh assumes a Windows MiKTeX location and also exports a PDF to its parent; direct commands keep the build local. `python scripts/depleted_tube.py verify tube_Q120` (or tube_Q60/tube_nominal) uses the included rational certificates; its build mode additionally uses NumPy/SciPy. `python scripts/preparation_geometry.py` uses exact fractions, and `python scripts/make_figures.py` uses NumPy/SciPy/Matplotlib. All data paths resolve within the copied package.

**Formalization:** The current 18-page paper extends the earlier 12-page workspace draft. The saved strict OperationalMain receipt covers fast_joint_service and its 27 local dependencies: actual nominal global existence and uniqueness, physicality, recovery after 4 ms and integrated service/resource accounts under explicit preparation assumptions. Additional unchanged roots cover stationary matched-rate and repair inequalities and saturating-donor algebra. Only fast_joint_service has a saved elaborated axiom interface in these selected receipts. The 0.1% preparation extension and depleted-donor tubes use exact arithmetic outside the kernel; uncertainty flow arguments, general moving-centre and storage results, and the logarithmic repair-delay conclusion remain conventional. Numerical trajectories and threshold estimates are illustrative. The stationary criterion is inherited from the companion paper. No global attraction, biological calibration or clinical claim is implied.

[Historical verification review](../../papers/P070-competing-biochemical-modules/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 30 selected modules, including shared dependencies. 17 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [OperationalMain.lean](../../proofs/DynamicSharedResource/OperationalMain.lean)
- [SourcePerturbation.lean](../../proofs/DynamicSharedResource/SourcePerturbation.lean)
- [RepairObstruction.lean](../../proofs/DynamicSharedResource/RepairObstruction.lean)
- [SaturatingDonorBounds.lean](../../proofs/DynamicSharedResource/SaturatingDonorBounds.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
