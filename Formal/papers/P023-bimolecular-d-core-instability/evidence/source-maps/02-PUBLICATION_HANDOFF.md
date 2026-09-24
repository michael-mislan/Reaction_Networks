# Publication handoff

Completed 2026-09-14T14:25:48-07:00. Post-proof **24/24 PASS**. The original campaign remains
43/48 PASS with five historical exploratory branches deferred; these are not
missing premises in the compiled R2 root.

## Delivered paper and reproduction package

- Final authoritative paper: `../Reactant_Bimolecular_Instability_Without_D_Cores.pdf` (workspace root), six pages.
- Editable manuscript: `reactant_bimolecular_instability.tex`, including bibliography.
- Reproduction archive: `../Reactant_Bimolecular_Reproducibility.zip`.
- Comprehensive follow-up arguments, assumptions and observations: `POSTPROOF_RESULTS.md`.
- All child certificates and scientific/formal mapping: `Supplementary_Information.md`.
- Running history and score: `POSTPROOF_LEDGER.md`, `POSTPROOF_REGISTER.md`.

The manuscript contains only the final critical counterexample proof. It gives
literal rates, positive equilibrium, exact Jacobian, an IVT construction of an
unstable nonreal eigenvalue, and an exhaustive child proof compressed to four
maximal selections. The independent Lean proof uses its original 25 padded
cases and exact coverage/embedding. The paper does not attribute its conventional
principal-restriction limiting argument to a new Lean theorem.

Earlier PDFs inside publication/ are intermediate versions; the workspace-root
PDF above is the deliverable. The isolated build directory resolved a Windows
file lock. Two LaTeX passes succeeded with zero overfull boxes or unresolved
references. All six final pages were rendered and visually inspected.

PDF SHA-256: `eec2ce48178d7a7473b2f918ae7aa3b3f67b6ac395dd9c95e7c9acf06d63bbcb`.
TeX SHA-256: `43eb739132e7aad58069463217f58a685a96761bf724f4899da60e80ebfcb439`.
Archive SHA-256: `0b3d03e6fe92fc051c7ee15718268d08ed29f601e3c504c0904f074133125c97`.

## Proof evidence and exact scope

The main result refutes universal R2 and R2-CF D-core necessity with four species,
six reactions and maximum product molecularity nine. Root source SHA-256:
`802c322dcae9a9feda0993572cbc98fcebf9a86e592d620949acf16497853fad`. The current root and all 20 local dependency source
hashes match the original strict receipt. Lean 4.30.0 and the frozen manifest
are unchanged. Both exported root declarations have only propext,
Classical.choice and Quot.sound in their authenticated axiom reports.

New strict receipts (verified true, exit zero, warnings as errors):

| File | What is formally checked |
|---|---|
| ElementaryFluxFamily.verify.json | Complete positive stationary flux parameterization and rate reconstruction |
| ElementaryParameterPolynomial.verify.json | Exact finite parameter characteristic polynomial, negative H certificate for T=100 and L>=100, and stable-control coefficient data |
| ElementarySpectralMargin.verify.json | Existence of an eigenvalue with real part at least two |

The conventional technical note completes the spectral implications for the
parameter region and strict stable control, qualitative moving-equilibrium
robustness under all six rate perturbations, and feed/dilution completion for
0<delta<2 with triangular transport of every child certificate. It also proves
R1 exclusion in arbitrary finite dimension, checks the inherited three-species
theorem for species minimality, derives the positive-mass obstruction, and
gives the dimensional conversion. These conclusions are not all newly compiled
Lean declarations; the note explicitly identifies their evidence.

The exact same-source stable operating point is T=2,L=1,s=1, with characteristic
coefficients (24,124,288,256), Delta2=2688 and H=626688. This corrects the earlier
comparison, where both the active stoichiometry and feeding had changed. The
old comprehensive report now records that correction. Small parameter and local
trajectory figures are illustrations, not stability proofs or periodic-orbit
certificates. The numerical experiment runs in seconds with one numerical thread.

R2P2, atom-resolved realization, nonlinear oscillation, and reaction/product
minimality remain separate open successors. No author identity, experimental
calibration or journal publication status has been invented; no submission or
external transmission was performed.

## Reproduction

The archive contains 24 local Lean modules, frozen descriptors,
four strict receipts, exact data, the paper and editable source, a sequential
strict replay program and README. Payload hashes and the complete local import
closure were validated; the extracted replay program passed --check-only with
all follow-ups. A fresh-machine Lean rebuild is not claimed.

Within this repository, use the canonical interpreter and existing bridge:

```powershell
.venv\Scripts\python.exe scripts/verify_proof.py proofs/DUnstableCores/Elementary/Resolution.lean --timeout 180 --declaration DUnstableCores.elementary_resolution --declaration DUnstableCores.reactantBimolecular_core_necessity_false
.venv\Scripts\python.exe scripts/process_guard.py run --timeout 240 --owner-label ELEMENTARY-PAPER -- .venv\Scripts\python.exe problem_workspaces/RAF_elementary_instability_without_Dunstable_core/publication/build_paper.py
```

Unchanged proof receipts were reused rather than recompiling for appearance.
The archive README gives independent extraction and replay commands. Do not run
lake update. Numerical illustrations require NumPy, SciPy, SymPy and Matplotlib.

## AGC and completion gate

AGC was helpful for freshness and scope, not for deriving the new algebra. Its
authorized same-frontier reconciliation recognized all three new authenticated
interfaces. The final checkpoint is retained as `agc_publication_final.json`.
Automatic mathematical docking remains unavailable for this minimal successor
spec (the documented NO_OPEN_FRONTIER limitation); no protected theorem graph
was altered to simulate closure. Administrative discovery guidance does not
invalidate the independently compiled source-level theorem.
