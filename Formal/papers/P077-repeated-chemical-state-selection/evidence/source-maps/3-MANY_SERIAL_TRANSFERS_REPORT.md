# Chemical-state selection through many serial transfers

## Result and evidence scope

This work extends the C3 serial-transfer theorem to arbitrary prescribed finite
horizons. It retains C3's literal four-resident chemical source, thirteen resident
channels, common precursor, complementary division, uniform intact-cell transfer,
fixed-time recovery of the selected cells, and proportional refill. It does not
introduce a fitness parameter, reset phases, replace returned cells, condition on
success, or resample unsuccessful histories.

The probability space is C3's composed **finite marked law**, with its physical
success records and analytical failure quotient. This is not a new identification
with an infinite trajectory-space process. All source constants and chemical
premises are inherited from the existing checked Lean modules. The contribution is
the finite-horizon composition, improved size-share bookkeeping, and explicit
rarity boundary. It is a source-specific quantitative extension, not a solution
of a named universal conjecture or a first demonstration of compositional selection.

The final verification evidence is `verification/resolution.json`; its `verified`
field and hashes, together with `COMPLETION_AUDIT.json`, determine the final status.
The rolling score and exact guide obligations are in `STATUS.md` and `TASKS.json`.

## 1. Source and protocol

Let N be newborn molecular/size scale, M the exactly retained compartment count,
and K the requested number of complete cycles. A ready compartment has size in
[N,2N). Its ancestry mark is used only in the analysis. Chemical readout is the
actual concentration test n_z/m > 2 and agrees with ancestry on the ready event.
The physical protocol never selects using the marks.

Each cycle charges precursor Q=4W_0, operates to Q=W_0 by deadline T=8/gamma,
processes a triggering division at the terminal growth event, retains exactly M
uniformly sampled intact endpoint cells, removes residual medium, and recovers
those same cells at Q=0 for 5376 model-time units. Refill uses their actual total
size. All later division phases are retained. The arbitrary-phase batch cap is
8M cells; a newborn-only 4M cap is not used for subsequent cycles.

The source assumptions include N >= 140000000000000000000,
0 < gamma <= 10^-11, the two specified stationary chemical roots, source-ready
populations, admissible finite clocks, and positive finite batch/recovery quotas.
The existential source theorems discharge roots, founders, clocks, and quotas.
The general error theorems expose these assumptions rather than hiding them in an
assumed reliable transition kernel.

Write B_i for ancestry size, W=B_H+B_L, q_i=B_i/W, C_i for retained cell count,
S=log(B_H/B_L), and L=log(C_H/C_L). Counts are positive on the certified event.
At epsilon=1/50 set

\[
g=\frac35\log4-\frac{19}{500}-\log\frac{51}{49},\quad
c=\frac{49}{800},\quad \rho=\frac{49}{204}.
\]

## 2. Baseline theorem and arbitrary finite horizons

For balanced newborn founders, define p_j=(1/2)c^j. The existing one-cycle
theorem supplies p_{j+1} and a strict size-log-odds gain exceeding g. These floors
remain positive real inequalities on integer counts; they are never rounded to
zero. A full history is a function Fin K -> Option ReadyPopulation. The `none`
branches retain the original failure mass. `historyGood` requires every actual
transition to meet its source relation. Conditional induction needs no
independence between cycles.

For the literal source history law, the all-prefix success probability is at least

\[
1-KE(N,M,T)-\frac{160000}{M}\sum_{j=0}^{K-1}(800/49)^j
 -\sum_{j<K}(s_{B,j}+s_{R,j}).                 \tag{1}
\]

Here s_B=Tq_B/J_B and s_R=M*5376q_R/J_R. On the event, every positive prefix obeys

\[
L_j-L_0>jg-\log2.                            \tag{2}
\]

The phase correction occurs once between endpoints. The theorem does not assert
monotone count gain between adjacent censuses. Arbitrary-phase founders use the
existing 2 log 2 endpoint allowance instead.

For completeness, with u=N/512000000000000000000 the literal chemical error is

\[
E=A+e^{-N/2500}+e^{-19N/500000}+MR(u),
\]
\[
A=Me^{-7u}+14Me^{-4u}+\frac{MTu}{42}e^{-15u/2}
 +Me^{-u}+\frac{MTu}{42}e^{-3u/2}+56Me^{-N/(35\cdot10^{12})},
\]
\[
R(u)=e^{-u}+2e^{-u/2}+e^{-8u}+16u e^{-31u/2}.
\]

The compiled uniform envelope is

\[
E\le [M(76+16u+Tu/21)+2]e^{-u/2}.             \tag{3}
\]

At fixed M,T this tends to zero as N tends to infinity. For every natural K,
the proof first chooses a finite even M controlling the finite rational transfer
sum, then a finite N controlling (3), then finite quotas with per-cycle allowance
delta=1/[1000(K+1)]. Each resulting mission has success probability at least
99%. Thus the parametric theorem has nonempty assumptions at every prescribed
finite horizon; two isolated numerical witnesses are not being substituted for
this availability argument.

## 3. Improved source theorem

Batch conservation gives W^-=4W_0 and B_i^- >= B_{i,0}. On the same weighted
transfer event used by C3,

\[
q_i^+\ge\frac{1-\varepsilon}{1+\varepsilon}q_i^-
\ge\frac{1-\varepsilon}{4(1+\varepsilon)}q_{i,0}.
\]

Recovery/refill preserve the selected cells' sizes and ancestry totals exactly.
Hence this is the next ready share. At any retained census C_i/M >= q_i/2;
that conversion is not paid recursively in the share floor.

Conditional on the complete endpoint, each selected weight is
w_{i,j}=m_j/(2N) times the type indicator. The exact without-replacement mean is
mu_i=(M/n)B_i^-/(2N). Since nN <= W^-,

\[
\mu_i\ge Mq_i^-/2\ge Mq_{i,0}/8.
\]

The existing finite subset variance bound, Var(X_i)<=mu_i, then gives two-type
transfer failure at most 16/(epsilon^2 M q_min,0). The proof uses the unchanged
uniform subset law, its actual weighted endpoint, and the actual recovery law.

Iterating q_j=(1/2)rho^j yields the **compiled improved mission bound**

\[
1-KE(N,M,T)-\frac{80000}{M}\sum_{j=0}^{K-1}(204/49)^j
 -\sum_{j<K}(s_{B,j}+s_{R,j}),                \tag{4}
\]

with the same measured gain (2). This is the guide's permitted second-moment
alternative. The optional exponential weighted-sampling theorem T1--T4 is not
claimed proved. Its absence does not reopen the completed second-moment result.

## 4. Certified witnesses and resource comparison

Both source instances use K=10, N=262144000000000000000000, gamma=10^-11,
balanced newborn founders, and confidence at least 99%.

| Instance | Retained M | Transfer budget, evaluated | Per-cycle batch/recovery allowances |
|---|---:|---:|---:|
| Baseline | 10^20 | 0.0001404802253766381 | each below 1/10000 |
| Improved shares | 10^15 | 0.000039563523736426656 | each below 1/10000 |

The population reduction is exactly 100000. The chemical error per cycle is
compiled below 10^-6 for both witnesses; the sharper rational replay of (3)
is far smaller. The mission service contribution is below 1/500. All these
budgets are unconditional contributions to the same original law.

The ten-cycle count-gain floor is exactly 10g-log 2. Outward rational series
enclosures in `replay_constants.py` place g in
(0.753771282,0.753771283) and that floor in
(6.844565640,6.844565642). These decimal enclosures are an analytic arithmetic
replay; the Lean source theorem states the exact logarithmic expression.

At fixed M=10^15 and the same N, exact formula replay with total service error
below 1/500 certifies 7 cycles using (1) and 13 using (4). These are bounds from
the stated allocation, not maximal achievable horizons or new trajectory
simulations. Failure of the sufficient inequality at the next horizon does
not imply actual type loss.

## 5. Rarity is a separate mathematical boundary

Positive retained counts satisfy C_H+C_L=M and L<=log(M-1). Therefore a
balanced-newborn history satisfying (2) through K must obey

\[
Kg<\log(2(M-1)).                             \tag{5}
\]

At fixed M, arbitrarily long histories cannot retain both counts positive while
sustaining this fixed cumulative gain. This does not prove extinction by the
ceiling: a history can instead cease to achieve the required gain. It makes no
claim that a lost ancestry cannot later be recreated as a chemical phenotype.

At a fixed endpoint of n cells with c marked minority cells, exact uniform
intact-cell sampling gives

\[
P(C_i^+=0\mid\text{endpoint})=\frac{\binom{n-c}{M}}{\binom nM}.       \tag{6}
\]

The combinatorial proof covers every M<=n, including zero/full samples. The
numerator is zero when n-c<M. The compiled product representation is the
product of (n-c-j)/(n-j) over j<M, using natural differences. In the admitted
regime M<=n-c and c<=n, a positive lower bound and an upper bound are

\[
\left(1-\frac{c}{n-M+1}\right)^M
\le P(C_i^+=0\mid\text{endpoint})
\le e^{-Mc/n}.                              \tag{7}
\]

The lower bound exposes the M sampled positions, rather than the guide R2's
c excluded positions. It is a valid alternative with a compiled strictly
positive base. Endpoint reachability under the chemical source is a distinct
question; (6) alone does not assign a probability to reaching that endpoint.

For n=400,M=100, exact losses for c=1,4,20 are 3/4,
13231647/42029596 (about .314817), and about .00268991. For c=20 the expected
retained count is five and survival loss is already small, but the one-type
2% Chebyshev relative-accuracy bound is 500 and hence useless. Survival and
accurate relative enrichment are different demands.

Equation (5) requires an exponential population scale with base e^g, roughly
2.125 per cycle, whereas (4) has sufficient geometric base 204/49, roughly
4.163. There is no contradiction: necessity, a conservative all-cycle
concentration guarantee, and actual endpoint extinction probabilities are
different statements. The remaining gap is explicitly left open.

## 6. Fixed-resource eligibility

At ready censuses take the analytical band q_min>=q_*>0. The source theorem
`sourceManyCycleLaw_eligible_probability` bounds the probability that every
eligible attempted cycle succeeds through K or the first successful band exit.
Its failure budget is K times the uniform band cycle error, including
16/(epsilon^2 M q_*). The crossing cycle and its returned state are included.
The original protocol does not inspect ancestry or stop at this analytical band.

For a transfer allocation delta_t>0, the second-moment sufficient band is
q_* >= 16K/(epsilon^2 M delta_t). At the refined ten-cycle witness and
delta_t=1/500 this is q_*=1/5000000. The terminal deterministic floor
(1/2)(49/204)^10 is greater than this threshold (about 3.19616e-7), so the
successful ten-cycle history does not exit that particular band early.

This statement alone does not guarantee K completed eligible cycles: early band
exit is allowed. The separate unconditional K-cycle theorems (1) and (4), with
their deterministic decreasing floors, supply that guarantee. A budget measured
only on one realized successful path is never used as unconditional confidence.

## 7. What was tested, rejected, and learned

1. **Baseline availability.** Exact rational pilots at K=10 and K=100 confirmed
   nonvacuous budgets. The source induction and the all-K existence theorem,
   not those two pilots, establish the formal result. Chemistry was not the
   bottleneck at the chosen copy scale; conservative transfer bookkeeping was.
2. **Heterogeneous phases.** All 70 four-cell samples from eight endpoint cells
   were enumerated exactly. Equal sizes give two-type relative failure 17/35
   at tolerance .02; within-type sizes {1,1,1.9,1.9} give 27/35, even though
   type counts and shares agree. At tolerance .5 the values are 1/35 and 13/35.
   This rejects count/share-only distributional closure. No chemical trajectory
   frequencies were inferred from this conditional diagnostic.
3. **Rarity.** Exact hypergeometric cases separate representation loss from
   relative weighted-total accuracy. Neither increased N nor a better chemical
   return theorem can by itself prevent uniform transfer missing a rare type.
4. **Sharper normalization.** Using both type intervals yields the corrected
   share map (1-epsilon)q/[4(1+epsilon)-2epsilon q]. From q_0=1/2 and epsilon=.02,
   its exact reciprocal is (308/155)(204/49)^j+2/155. Rational tests and a proved
   algebraic cap show at most a 155/154 improvement over the simpler floor.
   This is below .65% and does not change the exponential base or our round
   certified witness. An exact conservation-only endpoint (4,28) from initial
   sizes (4,4) attains the 1/4 minority-share loss. A better rate requires a
   source-level minority-growth estimate, not more denominator bookkeeping.
5. **Bounded route decision.** The guide explicitly permits the proved
   second-moment replacement. It already changes the ten-cycle population by
   five orders of magnitude. An additional exponential-moment library or
   minority-growth barrier is a successor, not a hidden unfinished task here.

Every numerical calculation uses the repository Python 3.11 environment.
All conditional subset calculations are exact, not Monte Carlo: there is no
seed, sampling uncertainty, or discarded failed trajectory. No astronomical
population or chemical state space was materialized. Strict proof attempts run
one at a time under the repository verification bridge and its process leases.

Formal errors were recorded and repaired: event-set extensionality, finite-card
instance equality, natural/real casts, function-composition normalization, and
strict unused-tactic lints. None was bypassed with `sorry`, axioms, warnings,
native numerical evaluation, or altered chemistry.

## 8. Mission accounts and interpretation

For K>=1 batches from newborn founders, charge each batch once. Fresh precursor
is at most (8K-4)NM; growth consumption at most (6K-3)NM; removed residual precursor
at most (2K-1)NM. The discarded cellular size is at most (7K-4)NM, using exact
intact transfer material balance and retained size at least NM. The exact balance
also applies separately to every resident molecular coordinate. The literal
source law returns a refilled ready state, so its terminal ready-to-run refill
is a separate stock, below 8NM. Including that stock gives total charged precursor
at most (8K+4)NM. It is not charged again as one of the K operating batches.

Mission duration is at most K(T+5376), excluding unmodeled handling time.
Each resident reservoir's gross exchange is bounded by the summed batch and
per-cell recovery quotas, at most K(J_B+M J_R). Quota capacity is not actual
consumption, free energy, or an analyzed depleting reservoir.

The improved ten-cycle witness has operating-batch precursor allowance
19922944000000000000000000000000000000000 size units, excluding the separately
bounded terminal refill of 8NM. Including that refill gives 84NM. Its duration allowance is
8000000053760 model-time units. These are extremely costly sufficient parameters.
M counts cells, not molecules, and is not converted using Avogadro's constant.
Changing time units does not establish faster physical kinetics. The theorem
establishes repeated measured chemical-state enrichment under a maintained
protocol, not laboratory feasibility, indefinite fidelity, fixation, innovation,
or autonomous fuel availability.

## 9. Lean source/declaration map and reproduction

All new Lean modules are in `proofs/SerialTransferSelection/`; dependencies remain
in the repository's pinned `mathlib4_project` environment.

| Module | Principal content |
|---|---|
| ManyCycleLaw | full history law, conditional probability induction |
| ManyCycleBaseline, ManyCycleMeasured | literal source connection, all-prefix size and measured-count gain |
| ManyCycleParameters, ChemicalEnvelope, GeometricEligibility, ManyCycleAvailability | ten-cycle arithmetic, uniform envelope/limit, exact sum, all-K parameter existence |
| ManyCycleInstance | `manyCycle_instance`, `tenCycle_instance` |
| ShareGeometry, ShareTransfer, ShareCycleGeometry | share recurrence, actual weighted means, selected recovery preservation |
| ShareCycleProbability, ManyCycleShare, ShareParameters | unchanged source cycle, all-K improved law and geometric budget |
| ManyCycleShareInstance | `manyCycle_share_instance`, `refined_tenCycle_instance` |
| MinorityBoundary | `finite_population_horizon`, count ceiling |
| TransferLoss, TransferLossBounds | `uniformTransfer_loss`, exact product and lower/upper bounds |
| EligibleHistory, SourceEligibleHistory | original-law eligible inspection, crossing-cycle convention |
| NormalizationRefinement | sharper denominator inequality, bounded improvement, conservation countermodel |
| ManyCycleAccounts | precursor, discard, service and time sums |
| ManyCycleResolution | `arbitrary_horizon_source_instance`, short source assembly |

From the repository root in PowerShell:

```powershell
.\.venv\Scripts\python.exe scripts/check_python.py --quiet
.\.venv\Scripts\python.exe scripts/agc.py checkpoint problem_workspaces/RAF_state_selection_many_serial_transfers
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/SerialTransferSelection/ManyCycleResolution.lean --timeout 900 --declaration SerialTransferSelection.arbitrary_horizon_source_instance --declaration SerialTransferSelection.refined_tenCycle_instance --declaration SerialTransferSelection.uniformTransfer_loss --declaration SerialTransferSelection.finite_population_horizon --output problem_workspaces/RAF_state_selection_many_serial_transfers/verification/resolution.json
.\.venv\Scripts\python.exe problem_workspaces/RAF_state_selection_many_serial_transfers/pilot.py
.\.venv\Scripts\python.exe problem_workspaces/RAF_state_selection_many_serial_transfers/weighted_pilot.py
.\.venv\Scripts\python.exe problem_workspaces/RAF_state_selection_many_serial_transfers/normalization_pilot.py
.\.venv\Scripts\python.exe problem_workspaces/RAF_state_selection_many_serial_transfers/frontier_pilot.py
.\.venv\Scripts\python.exe problem_workspaces/RAF_state_selection_many_serial_transfers/replay_constants.py
```

The verification bridge chooses the correct Lean working directory and treats
warnings as errors. No dependency update is needed. Arithmetic replay does not
replace source compilation. Generated verification/publication evidence has not
been staged or committed by this proof agent.

## 10. AGC and final handoff

AGC was used at entry, new proof structures, proof failures, and closure checks.
It initially reported the missing specification/publication accurately; the
requested publication action was followed by a fresh checkpoint. Later checks
reported CURRENT and tracked failed declaration attempts. They did not supply
new mathematical lemmas. One dependency Lean error was classified as infrastructure
failure and elicited an unhelpful identical-retry suggestion; the actual compiler
diagnostic was inspected and the proof fixed. The mathematical progress came from
source reuse, conditional induction, exact geometry, and discriminating small tests.
AGC remains a freshness/proof-state diagnostic, not kernel evidence.

An earlier closure checkpoint returned CURRENT with classification
`current_with_unbound_authored_closure`, requesting authority-integrator review.
The final checkpoint after ledger reconciliation returned CURRENT with
`current_with_unbound_authored_route`; it selected an earlier ledger route for
share-cycle and loss-bound proofs that are now compiled. This limits AGC's
usefulness as a completion assessor here; its authored-route suggestion is
proof-neutral and does not override the current strict receipt. A bounded attempt to use the supported
`post-proof-publish` command returned `AGC-POST-PROOF-E001: no synchronizable live
frontier: NO_OPEN_FRONTIER`. This campaign has no declared frontier authority.
Accordingly, the mathematical roots are green in the evidence ledger, but no AGC
`ClosedRoot` or authority publication is claimed. No theorem graph was silently
advanced, and no additional interface infrastructure was fabricated to change
that administrative status. The strict compiled theorem and 50 guide outcomes
are the completion evidence.

The remaining genuinely open quantitative question is how far the sufficient
horizon/population rate can be moved toward the necessary count-odds ceiling
while keeping the same chemistry and intact uniform transfer. That would require
a new minority-growth or cumulative-fluctuation theorem. It is explicitly outside
the completed finite-horizon endpoint and must not be confused with a claim of
permanent coexistence at fixed M.

Final guide completion: **50/50 PASS; ROOT-BASELINE GREEN; ROOT-MANY GREEN**,
at the finite marked source-law scope described above. Strict root receipt:
`verification/resolution.json`, root source SHA-256
`fe47d937a668e2d82b3d4aff19ecf303ac6852dfa8f3768296b9fda23088589d`.
The four exported declarations use only `Classical.choice`, `Quot.sound`, and
`propext`; there is no `sorryAx` or added source axiom. The completion audit
checks current source/dependency hashes and maps every guide item to evidence.
