# Extension and publication report — completed handoff

Baseline commit: 13eef117f44d6a5c149bc39ce4b0ab36d63b93d3.
Original campaign remains 60/60; extension register progressed from 0/36 to 36/36.
Brief read in full. Canonical runtime and numerical smoke passed. Original
exact certificate reproduced. Entry AGC CURRENT; it repeats the original
source-link obligations and does not contain the extension graph yet.

Baseline corrections: the colony alias is a local family in an equivalence
level set, not an open subset of full parameter space. Within-cell induction
q_ST(1)-q_ST(0) is distinct from division-associated daughter production
2b_i L_i(T); both will appear in the final estimand. The full stochastic
theorem remains conventional; the existing Lean source only proves finite
algebra. No new source drift was found in that interface.

Contribution target: randomized stopping yields a finite-state source inverse;
monitored delayed daughter readout preserves joint-kernel identification;
direct feature intervals infer induction with unknown nuisance rates; sister
concordance predicts extinction differences invisible to mean growth.
Strongest biological requirement: an externally calibrated, label-aligned,
nonperturbing state marker, with independent errors conditional on the source,
and a homogeneous Markov phenotype model. Existing cell-cycle reporters do
not automatically meet that requirement.

Scientific nodes at entry: X1-X5 and publication P were RED-OPEN. They are
now closed at the conventional proof/publication level described below.

## Deliverable and exact proof status

The 14-page research paper is `stopped_lineage_identification.pdf` in this project root. Its editable source is `paper/main.tex` with sections and references in that directory. The paper contains the final source-to-observation proof chain and the requested finite-data and biological consequences. Discovery-only three-view lemmas and certificate campaigns are omitted; the historical ledger preserves them.

The full stochastic results are conventional mathematical proofs, **not a fully compiled Lean proof of the stochastic root**. The aggregate `proofs/PhenotypeIdentification/Postproof.lean` imports the original Resolution and new Resolvent, DelayedChannel and OffspringOrder modules. Strict receipt `evidence/postproof_lean.json` reports verified=true, exit 0, empty stdout/stderr and 137.687 seconds. Lean checks finite resolvent cancellation, the two-state rational target identity, rectangular delayed-channel cancellation and the offspring polynomial identity. It does not check the source construction, killed-process integral, concentration theorem or ODE comparison. The frozen environment is Lean 4.30.0; no warnings, sorry or custom mathematical axioms are admitted. This boundary appears in the abstract and appendix.

## Final critical proof path

1. Construct the nonexplosive finite-state chronological branching source and its PGF. Stopping at the first division/death exposes H=Q-diag(b+d) and exit matrix B=[d | bK]. The limited binary endpoint has a preparation/rate alias; this is not an impossibility theorem for all fluctuation data.
2. Compete that event with an independent exponential deadline of known rate lambda. Integrating the killed semigroup gives A=lambda(lambda I-H)^-1 and D=(lambda I-H)^-1 B. Calibrated initial/endpoint and joint daughter records recover these matrices, then H=lambda(I-A^-1), B=lambda A^-1 D. The proof permits singular H, complex spectra and any finite number of states.
3. A known delayed daughter reading retains an interruption flag for any division/death before the read. Its channel stacks E exp(tau H)^T above missing survival mass, so it has full column rank for every finite delay. Recover H from founders, birth/death rates from event totals, then the channel and joint K. Daughter processes are independent given both birth states; sisters need not be independent given their mother.
4. In two states, q_ST=lambda pi_T M_ST/det(M), M=L J L^T. Five features per arm plus labelled calibration probabilities yield simultaneous Hoeffding regions. Exact rational interval propagation gives at least 95% coverage uniformly over unknown nuisance rates, founder masses and K. Denominators not separated from zero produce unresolved intervals.
5. Mean evolution depends on G=Q-diag(b+d)+2diag(b)L. The perturbation K+epsilon(1,-1,-1,1) preserves daughter marginals and G but increases its offspring PGF by epsilon(x_S-x_T)^2. Cooperative ODE comparison gives weak extinction ordering. Unequal death rates and positive b_i epsilon_i give a strict cubic small-time difference; common state-independent demographic rates give a zero-effect boundary.

The contract requires positive founder support, finite rates, homogeneous Markov states, calibrated full-column-rank nonperturbing markers with conditionally independent errors, aligned labels across arms, independent experimental units and reliable event/interruption observation. A daughter-kernel row is recoverable only where division rate is positive.

## What we tested and learned

All experiments used canonical repository Python, single-thread numerical settings and bounded process leases. The main extension run takes about three seconds and figure generation about eight. No brute-force search or large simulated branching population was needed. Inputs, seeds and outputs are retained in `experiments/postproof.py` and `evidence/postproof.json`.

| Testable hypothesis | Result and implication |
|---|---|
| Resolvents remove the fixed-time spectral restriction | Exact rational directed three-cycle, reducible/singular and stiff examples recover H,B; the semigroup integral supplies the general proof |
| Finite daughter delay destroys rank | Refuted by an explicit left inverse; singular values nevertheless deteriorate, separating identification from precision |
| Founder features isolate switching with unknown demographics | Rational target and exact interval arithmetic succeed; a large joint nuisance optimizer is unnecessary |
| Every finite dataset yields a useful interval | Refuted by the retained 20-founder unresolved example; determinant clipping would be invalid |
| A continuous unknown-nuisance class admits a prospective guarantee | Exact interval enclosures separate explicit narrow null/alternative boxes; a source grid is not used as proof |
| Joint inheritance has an effect invisible to means | Same G but ordered extinction, proved analytically and illustrated numerically |
| Age structure is absorbed by one constant hazard | Erlang-2 apparent rates differ across deadlines; this is a model obstruction |
| Arbitrary delayed reporter maturation preserves identification | Identical daughter-channel columns destroy K recovery even if founder H is known |

The directed three-cycle has H=[[-3,2,0],[0,-3,2],[2,0,-3]], lambda=3/2 and A=(1/665)[[243,108,48],[48,243,108],[108,48,243]]. Its complex spectrum tests the reason to change stopping design. Singular examples show why H itself must not be inverted. These are implementation checks, not substitutes for the finite-m theorem.

With 50,000 founders per arm and 100,000 labelled calibration reads per state, the worked synthetic dataset gives switching intervals [0,0.160785545] and [0.523161242,1.497817962]. The exact-endpoint induction interval is approximately [0.362375697,1.497817962], displayed outward in the paper as [0.362,1.498] per hour; truth is 0.8. The inference code receives counts, calibration counts and lambda, not nuisance values. Seed 20260922 and all category counts are retained. In 300 repetitions with fresh calibration the interval covers truth and excludes zero in all 300. The exact binomial Monte Carlo interval for either proportion is about [0.987779,1]; this diagnostic is not the coverage proof.

The prospective test allows founder mass, reverse switching, birth and death rates to range over narrow continuous boxes, with arbitrary stochastic K. At n=n_c=1,000,000 per arm/per calibration state, all returned intervals on the simultaneous coverage event lie inside [-0.129436,0.129436] under the null and [0.439703,1.298899] under the alternative. Threshold 0.4 has error at most 0.05 under either class. These expensive sufficient budgets are not asserted necessary. Interval dependencies, calibration subtraction and determinant conditioning contribute to the conservatism. A separate stopped-path KL/Pinsker bound proves an intrinsic small-effect obstruction for the immediate record or founder-only coarsening; it does not apply unchanged to additional delayed daughter trajectories.

The design figure compares deadline rates on identical sources with both equal founder counts and equal expected founder-hour budgets, holding calibration sample count fixed. Rounded expected counts are a design diagnostic, not another prospective theorem. `evidence/design_cost.json` retains them. A physical cap has total-variation reserve at most exp(-lambda L); L=14/lambda gives less than 10^-6, but the capped kernel is not an exact resolvent.

The baseline concordance perturbation changes 24-hour extinction by about 0.0005464. Guided by the strict cubic coefficient, a second synthetic source with greater death contrast gives about 0.054116 while preserving means exactly. These ODE effect sizes are floating-point outputs, not interval-certified magnitudes or biological measurements. For Erlang-2 division with phase rate 1, deadlines 1 and 2 produce apparent constant birth rates 1/3 and 1/4. No homogeneous one-state generator fits both.

## Literature and experimental interpretation

The focused primary comparison covers Greene, Gevertz and Sontag's controlled-ODE induction result; Gunnarsson, Foo and Leder's switching/demographic inference; Wu, Gunnarsson, Foo and Leder's drug-screen framework; Mohammadi et al.'s lineage-tree HMM; Metzner et al.'s established resolvent generator method; Fitzsimmons and Pitman's stopped-process potentials; and Bertacchi and Zucca's generating-function order. The paper gives direct DOI/arXiv references. No priority claim is made for resolvents, induction identification or PGF comparison in isolation. The contribution claimed is the explicit connection to this observation protocol, delayed channel, finite-data target and inheritance-dependent extinction consequence. This focused comparison is not an exhaustive priority proof.

AU565 lineage imaging provides one coherent experimental architecture, not fitted model parameters. Reported 30-minute imaging and 96-hour follow-up are distinguished from ideal instantaneous event detection. Nuclear/cell-cycle reporters are not asserted to be calibrated tolerance-state reporters. Every numerical rate, kernel and marker in the examples is synthetic, as the provenance table states. Population doubling time is not a single-cell exponential division hazard. Unknown reporter memory, unobserved age phases and arbitrary shared environments remain outside the stated source contract.

## Review corrections and reproducibility

The binary alias is a family in an observation-equivalence level set, not an open subset of full parameter space. Division-linked daughter production 2b_i L_i(T) is distinct from within-cell induction. The KL lower bound is restricted to the paths it actually controls. These scope corrections are reflected in the final paper.

Run from the repository root using `.venv/Scripts/python.exe`. The concrete experiment paths are under this workspace's `experiments/`. Use `scripts/process_guard.py run --timeout 120 --owner-label NGI-postproof --` followed by the absolute canonical interpreter and `experiments/postproof.py` for the numerical suite. For figures, use the same guard with timeout 90 and `experiments/paper_figures.py`. `paper/build.py` uses three pdflatex passes with package installation disabled; run it through the guard with timeout 300. Strict Lean verification is:

```
.venv/Scripts/python.exe scripts/verify_proof.py proofs/PhenotypeIdentification/Postproof.lean --timeout 420
```

The build script locates the project relative to itself and copies the PDF to this root. Source is `paper/main.tex`, `paper/sections/*.tex` and `paper/references.tex`. Final build metadata and PDF SHA-256 are in `evidence/paper_build.json`; aggregate checks are in `evidence/paper_qa.json`. Rendered pages and logs are under `paper/tmp/pdfs/`. All 14 pages were visually inspected, including figures, equations and references; affected pages were rechecked after correcting citations, table spacing, diagram clipping, a commit identifier overflow and an equation label. The final build has no LaTeX warnings.

The recorded baseline commit is the state inspected at entry, not a claim that it already contains these new working-tree outputs. No dependency update or generated-evidence commit was made.

## AGC and stopping criterion

Entry, structure and completion checkpoints are retained as `evidence/agc_postproof_*.json` (AGC emits YAML despite these historical filename extensions). AGC reports CURRENT with an unbound authored route and retains the baseline canonical cut. It helped keep source-law, robustness and proof-status obligations visible, but supplied no new proof argument. Checkpoints are proof-neutral; they do not verify mathematics or close canonical authority nodes. Local scientific closure is recorded separately in `HYPOTHESIS_GRAPH.md`.

No required conventional scientific or publication item remains open in the 36-item extension scope. Full stochastic Lean formalization and biological calibration remain unresolved outside this completed scope. The compiled finite algebra does not erase that boundary. Completion means the explicit observation-design theorem package and requested paper are delivered, not that every biological version of non-genetic inheritance inference is solved.
