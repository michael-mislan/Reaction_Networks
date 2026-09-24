# Reproducibility supplement

The accompanying paper contains the final conventional proof. This supplement records executable interfaces and exact-computation boundaries. Evidence classes: K = Lean kernel verification; C = conventional proof; E = exact finite computation; N = numerical illustration. C/E is not K.

## Source and protocol

The inherited seven-species source and its coefficients are unchanged. Regimes W and O change the declared parameter intervals and startup deadline. O also changes the physical operation law to biased complementary partition and independent imperfect product recovery, with complete product clearance. F changes the fuel invariant to H+W=64 and admits two minority residents. None of these operations adds or resets a resident label. The inherited Main.lean is preserved; Postproof.lean imports four new modules.

The full source is explicitly given in the paper. Source simulation uses the inherited STOICH and rates functions. Product credits count terminal removed molecules; reverse production can reduce stock. Both actual daughters are refilled and charged before retention. A failed or outside-region trajectory is not normalized away.

## Exact absorption recurrence

Fix total residents r and initial minority j. Put transient mass t_0(j)=1, except that an initial endpoint is absorbed with zero expenditure. At step k, for each transient y, send mass t_(k-1)(y)*(r-y-1)/(r-2) to y-1 and t_(k-1)(y)*(y-1)/(r-2) to y+1. Remove newly absorbed masses into a(k,0) or a(k,r); retain all remaining masses for the next step. Stop after L=64. Exhausted transient mass is a failure, not redistributed. The script asserts absorbed plus transient mass is exactly one.

For each endpoint b define v_b=sum_k a(k,b) and s_b=sum_k k*a(k,b). The exact source lower bound is

    (c - 80*epsilon)*v_b - 80^3*beta*s_b - 3216*tau - d,

where c=2147232289/2147483648, epsilon=1/10^7, beta=5/10^11, tau=1/10^7, and d=1/10^12. This sums the conditional core lower bound at each actual spent-fuel value. The two clocks are compared at fixed time tau; no stopping-time horizon substitution occurs. Removing late absorption paths costs at most d. The 64 exponential holding-time upper comparison is valid until absorption or fuel exhaustion; unused exponentials can be appended after absorption.

All 216 admitted (r,j) pairs, j in {0,1,2}, 8+j <= r <= 80, are evaluated by rational arithmetic. The worst selected endpoint is r=10,j=2:

    v_0 = 675247821429526785890499475507935979615 /
          680564733841876926926749214863536422912
    s_0 = 24981573789484567970908456334429570891 /
          10633823966279326983230456482242756608
    q_F = 353843849988858058737189145333276639679672751198608372719 /
          356811923176489970264571492362373784095686656000000000000

Thus q_F > 2479/2500. For the opposite endpoint at the specified mixed preparation:

    q_switch = 2671682134717935700320252735506835532378141803715572719 /
               356811923176489970264571492362373784095686656000000000000

This exceeds 37/5000. These are lower bounds, not exact source probabilities. Complete absorption results are in experiments/fuel_absorption.json. The runtime uses Python fractions.Fraction throughout.

## Core certificate and operation law

experiments/replay.py recomputes the inherited core; experiments/operation_certificate.py uses the same integer uniformization recurrence with payoff P(Bin(p,eta)>=4)*P(8<=Bin(n,theta)<=n-8). All 3240 states and all n=8,...,80 newborns are included. The terminal payoff is rational before floor rounding. With eta=9/10 the recorded theta numerators over 2^31 are:

| theta | Numerator |
|---|---:|
| 49/100 | 2147213192 |
| 12/25 | 2147153442 |
| 9/20 | 2146619325 |

Only theta=12/25 is needed for the adopted O theorem. The other points are a small diagnostic, not coverage evidence. Analytic binomial differentiation, symmetry and recovery monotonicity prove coverage of the continuous parameter intervals. No numerical optimization over rate corners is used.

The integer row sum is D=321600, scale S=2^31, and there are 3216 time blocks. Downward-rounded Poisson weights use the 25-term alternating lower sum for exp(-1); weights beyond index 12 vanish at this scale. Row products and weighted sums are bounded below 2^63 as shown in the paper. E validates the executed recurrence; generic positivity/iteration lemmas have K support. There is no kernel-replayed certificate data file connecting the complete integer output to the CTMC theorem.

## Lean scope

The inherited strict receipt is main_verification.json. The new strict receipt is postproof_verification.json, verified=true, exit_code=0, stderr empty, warning-as-error=true, Lean 4.30.0. Postproof.lean and its nine local dependencies passed. Only the standard Classical.choice, Quot.sound and propext occur in the printed decisive axiom lists. A subsequent exact AGC-requested invocation reused the matching verified artifact.

| Module | Verified content | Boundary |
|---|---|---|
| RateBudget | Integer prefix bound; finite Taylor exponential estimate; exact improved budgets | Full source clock coupling is C |
| OperationKernel | Central derivative sign and nonnegative product monotonicity | Derivative identity and distributional endpoint transfer are C |
| CorrectionWalk | Rate factorization, embedded down probability, recursive fuel values, two-step instance | General absorption-law interpretation and complete 64-step table are C/E |
| SelectionRound | Exact selection tails and integer readout separation | Actual population event identification is C |

These modules are useful portions of the argument, not a claim of a fully formal probability theorem. Failed parser/elaboration attempts are archived diagnostics and are not accepted evidence.

## Reproduction commands

Run from the repository root, using the existing pinned environment. Each command below is one line in PowerShell. No environment or dependency update is required.

```powershell
.venv/Scripts/python.exe scripts/check_python.py --quiet
.venv/Scripts/python.exe scripts/smoke_numerics.py
.venv/Scripts/python.exe problem_workspaces/RAF_TINY_COMPUTER/experiments/replay.py
.venv/Scripts/python.exe problem_workspaces/RAF_TINY_COMPUTER/experiments/operation_certificate.py
.venv/Scripts/python.exe problem_workspaces/RAF_TINY_COMPUTER/experiments/fuel_absorption.py
.venv/Scripts/python.exe scripts/verify_proof.py proofs/TinyProgrammableChemicalFactory/Main.lean --timeout 600
.venv/Scripts/python.exe scripts/verify_proof.py proofs/TinyProgrammableChemicalFactory/Postproof.lean --timeout 600
```

The small exact calculations took seconds. For optional numerical reproduction use the process guard, not an unbounded launch:

```powershell
.venv/Scripts/python.exe scripts/process_guard.py run --timeout 120 --owner-label TINY-postproof -- .venv/Scripts/python.exe problem_workspaces/RAF_TINY_COMPUTER/experiments/population_followup.py
.venv/Scripts/python.exe scripts/process_guard.py run --timeout 120 --owner-label TINY-elementary -- .venv/Scripts/python.exe problem_workspaces/RAF_TINY_COMPUTER/experiments/elementary_pilot.py
.venv/Scripts/python.exe problem_workspaces/RAF_TINY_COMPUTER/publication/make_figures.py
```

Build paper.tex using pdflatex twice from publication/. All figure PDFs are local. The final deliverable is copied to the workspace root. PDF_QA.md records page review. source_manifest.json hashes sources, finite outputs, strict receipts and the delivered PDF; hashes are reproducibility metadata, not proof evidence.

## Literature comparison

The main paper cites primary sources for programmable autocatalysis (Kriukov et al.), compositional heredity and selection (Matsubara et al.), compartment growth/competition (Lu et al.), chemical kinetics compilation (Soloveichik et al.), and thermodynamic interpretation (Rao and Esposito). The comparison is bounded; no priority or named-conjecture claim is made.

The existing internal manuscript is *Finite-batch selection between inherited chemical states under a shared limiting resource*, located in RAF_resource-limited_competition_between_inherited_chemical_states/Finite_Batch_Selection_Research_Paper.pdf. Its explicit four-species source uses endogenous growth with a shared limiting precursor, maintained resident feeds, a nutrient hitting time, and finite stopped-law Lean results. The present source instead supplies a fixed-horizon, seven-species, small-inventory protocol with external product retention. Neither theorem subsumes the other. The internal paper's abstract and source scope were inspected; its proof was not freshly rebuilt in this follow-up.
