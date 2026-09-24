# Finite fuel/waste reservoirs: mathematical handoff

Date: 19 September 2026. Guide scope complete: **48/48 PASS**. The consolidated strict receipt Resolution.verify.json reports verified=true, exit_code=0, and empty compiler/probe diagnostics. The exact chosen scope of the metered-food coupling is distinguished below.

## Result and exact scope

The specified repeated-operation extension has been proved for the literal twenty-label count reactor with a persistent finite fuel/waste bath. The proof uses the changed, state-dependent stochastic source. It does not import the maintained-bath trajectory law or assume that a successful cycle occurs.

The principal files are `proofs/FiniteReservoir/Mission.lean`, `InverseDesign.lean`, and the consolidated `Resolution.lean`. `finite_bath_horizon` is the general parameterized operational theorem. `pure_inverse_design` and `finite_reservoir_repeated_operation` combine confidence, output demand and reservoir tolerance. `example_mission` gives a concrete instance. Strict receipts are stored in this workspace.

This is an extension of the operating theorem specified by the supplied guide. It is not presented as a named conjecture of the literature cited by the guide, or as the first theory of finite reservoirs.

The main stochastic and thermochemical results are kernel-checked Lean proofs. The metered-food corollary has compiled inventory/rate-agreement lemmas and a separate conventional coupling proof. A separately formalized metered path-measure construction is not claimed; see `METERED_FOOD_COUPLING.md`.

## Literal model and hypotheses

The state consists of internal counts N=(u,w,x,c1,c2,z) and bath counts (f,p). The bath's reference capacity R is fixed and positive. The driven forward rate is d(f/R)x; the reverse rate is d(1/8000000000)(p/R)uw/V. A forward jump changes the bath by (-1,+1); a reverse jump changes it by (+1,-1). All other propensities, falling-factorial conventions and event labels are the original ones.

The two food arrival intensities remain V, and species washout intensities remain their counts. The original molecular intervention law is used in full, including unsuccessful outcomes. Its food boluses are charged, and its thinning/withdrawal leaves the bath unchanged. Each cycle has three time units before output collection and one collection unit. Actual internal and bath endpoints become the next cycle's starting state. No bath reset, hidden fuel replenishment or success conditioning is introduced.

The general `Parameters M` class requires:

- positive reference capacity R;
- release speed r in [19,21];
- nonnegative d with dM≤R/25;
- conserved bath inventory f+p=M.

For every possible bath composition in that class, the effective forward coefficient lies in [0,1/25] and the reverse coefficient lies in [0,1/200000000000]. This is the uniform RateBox used by the probability proof.

Candidate A has M=R, initially (f,p)=(R,0), and admits the original publication interval d∈[1/50,1/25]. The stochastic bounds in fact allow d down to zero. Candidate B has M=2R, initially (R,R), and d=1/50. Both constructors and their coefficient hypotheses compile. Zero fuel or zero waste is allowed along a path; the unsupported consumption rate vanishes at the corresponding boundary.

The initial internal population is established catalytic stock satisfying `Restart V`. A nonempty witness is N=(0,0,V,0,0,0). The theorem is not a food-only-origin or seed-preparation theorem.

## Joint probability statement

For V≥200000000000, any admitted initial full state, any finite mission length m and any admitted policy based on returned histories, let E_m be the event that every cycle:

1. returns to the original internal restart set;
2. collects at least ceil(V/56) template equivalents and ceil(V/1080) free X molecules;
3. uses at most 5V food molecules of each species, counting its bolus;
4. records at most floor(V/5) gross driven events.

Free X is included in template-equivalent output; these are not disjoint counts.

The full normalized history law satisfies

    P(E_m) ≥ (1-e(V))^m ≥ 1-m e(V),
    e(V) ≤ 101 exp(-V/10000000000).

Lean uses `ENNReal.ofReal` for lower bounds, so a negative linear lower bound is correctly truncated at zero. The product and linear bounds use conditional iteration, not independence of successive cycles. A general conditional-history interface also permits a richer measurable observation history, provided it obeys the proved literal conditional cycle law.

Actual finite reaction traces are present almost surely. On the same event, their net internal template production is at least

    (m/56 - 161/160) V.

Thus sufficiently long certified output cannot be explained entirely by initial stock. The trace production mark includes both forward template destruction and reverse template creation in the driven pair.

## Reservoir prefixes and inverse design

For every supported chemical prefix, the proof establishes the exact natural-count identity

    f_end + F = f_start + P,

where F and P count the two distinct directed driven labels. Gross service is F+P. Waste changes by the opposite signed amount. The history trace retains these labels even though the operational endpoint counters record gross service.

Let B=m floor(V/5). On E_m, every chemical prefix of every cycle, including recovery and collection, obeys |f-f_initial|≤B and |p-p_initial|≤B. This statement concerns all prefixes, not only the final mission endpoint.

For pure fuel, R≥B/rho gives f/R∈[1-rho,1] and p/R≤rho. For the loaded bath, the same size condition gives both activities in [1-rho,1+rho]. When 0<rho<1, the loaded bath's force deviation obeys

    |log(a_F/a_P)| ≤ log((1+rho)/(1-rho)).

An explicit noncircular design for m>0, δ>0, rho>0 and requested outputs Q_I,Q_X is:

    V = max(200000000000,
            ceil(10000000000 log(101m/δ)),
            ceil(56 Q_I/m), ceil(1080 Q_X/m)),
    R = max(1, ceil(m floor(V/5)/rho)).

The natural ceilings handle integer sizes; Lean implements the maximum in nested form. At r=20,d=1/50 with pure initial fuel and the explicit restart witness, the probability of the joint event containing operational success, both output demands and every-prefix fuel tolerance is at least 1-δ. To interpret this as nontrivial confidence and a positive fuel floor, choose δ<1 and rho<1. The proved theorem remains valid outside those useful ranges.

## Concrete certified example and dimensions

The example uses V=200000000000, m=100, R=40000000000000, rho=1/10, r=20 and d=1/50. The initial internal state is all-free X with count V; the pure bath starts with R fuel and zero waste.

On one event of probability at least 999979/1000000 = 0.999979:

| Quantity | Certified value or bound |
|---|---:|
| Mission duration | 400 source time units |
| Template-equivalent collection | at least 357142857200 |
| Free-X collection | at least 18518518600 |
| Food U use, including boluses | at most 100000000000000 |
| Food W use, including boluses | at most 100000000000000 |
| Gross driven events | at most 4000000000000 |
| Fuel activity at every prefix | between 0.9 and 1 |
| Waste activity at every prefix | between 0 and 0.1 |
| Net internal synthesis | at least (100/56-161/160)·200000000000 |

The analogous loaded bath starts with R fuel and R waste, has total inventory 2R, and satisfies both activity tolerances with the same gross allowance and d=1/50. Its operating theorem and force corridor are proved separately.

Counts, V and R are in the model's reference count units. Activities are dimensionless. Time is in the source's kinetic time unit; the report does not invent a conversion to seconds or liters. Potentials below are in dimensionless thermal units. Conversion to physical volumes and energies needs the chosen reference concentrations, kinetic unit and temperature. The count inequalities themselves do not depend on that conversion.

## Thermochemistry and the lifetime interpretation

For a species count n at reference count C and standard potential g, use

    n g + log(n!) - n log C.

The internal standard potentials are the C0 assignment: 0,0,-log10,-log10,-log10,-2log10. The bath standard potentials are g_F=log10+log8000000000 and g_P=0.

For a supported forward transition, the reverse propensity is evaluated at the post-state. The exact ratio is

    8000000000 · f/(p+1) · R_P/R_F · Vx/((u+1)(w+1)).

Lean proves that this equals exp(-ΔG_total), proves the literal forward neighbor update, and proves exact telescoping of bath-potential increments. The proof covers initially empty waste because the neighboring reverse propensity contains p+1. It neither evaluates a physical chemical potential at log0 nor substitutes a same-state forward/reverse ratio. The general-capacity identity specializes to the exact equal-capacity source used by the mission theorem.

A constant maintained-affinity work value multiplied by net fuel service is not the changing bath's exact free-energy change. The prescribed food feeds, withdrawals and harvesting apparatus remain external operations; the chemical identity does not make the entire setup a closed equilibrium system.

Forward drive destroys template in this source. Reliable output and gross turnover therefore do not imply positive net fuel consumption. The compiled conditional obstruction is: if net service J satisfies J≥m j_* V and fuel_end=fuel_initial-J≥0, then m j_* V≤fuel_initial. No positive j_* premise is established or smuggled into the operating theorem.

## Metered food

The compiled history counters include every pulse bolus and are nondecreasing at chemical, cycle and mission prefixes. With preparation charges P_U,P_W, allocate P_U+5mV+1 and P_W+5mV+1 molecules. The spare molecule makes both remaining inventories strictly positive on the successful event.

`MeteredFood.lean` proves that the full propensity vector agrees with the original one before stockout, and proves the all-prefix no-stockout inequalities. `METERED_FOOD_COUPLING.md` gives the exact common-randomness construction, using identical waits, labels and pulse outcomes until shortage, with an explicitly absorbing shutdown convention. On the original successful event no shortage occurs, so the metered process has at least the same mission success probability. This final path-measure coupling argument is conventional mathematics, not a separate Lean construction. Passive concentration-dependent food tanks are outside this corollary.

## Hypotheses tested and what they taught us

| Hypothesis or diagnostic | Test | Result and effect on proof |
|---|---|---|
| Independent forward/reverse coefficients preserve C2's local estimates | Exact rational drift, noise, phase, clock and gross-intensity arithmetic | Passed. Motivated the global RateBox proof rather than a trajectory comparison. |
| Output might require sustained fuel abundance | Six deterministic eight-cycle Radau runs with retained bath histories | Near-exhausted fuel still supported substantial output. Rejected fuel necessity as an unsupported interpretation. |
| Bath boundaries might invalidate supported updates | 9072 small supported-event checks | Passed nonnegativity and conservation checks; informed exact supported-source bridges. |
| Same-state ratios might stand in for neighboring detailed balance | 486 exact neighboring-ratio checks and a later 486-case potential pilot, including 162 zero-waste cases | The neighboring identity passed; same-state reverse vanishes at zero waste and is unsuitable. |
| A closed stopped success event might transfer directly | Small strict-event model | Closed stopped success was 1 versus physical 1/2; strict success was 1/4 for both. Required strict active success in the physical bridge. |
| A finite-bath path could be treated as a fixed-d path | Inspection of concrete generators and source interfaces | Rejected. Rebuilt the actual augmented source inequalities and physical law; reused only generic kernel machinery and unaffected source algebra. |
| Formal bridge failures indicated a mathematical obstruction | Inspected compiler diagnostics at every pilot | Failures were parameter inference, projections, definitional reductions, recursion or linter issues. No new numerical counterexample emerged. Explicit source identities and typed states resolved them. |

The deterministic maintained baseline had minimum Q_I/V≈0.26563859674247214 and Q_X/V≈0.12305116308482425. At R/V=0.001, final fuel activity was about 2.38×10^-10 while minimum Q_I/V≈0.2705192. The conserved bath was retained across pulses and directed accounting residuals were below 6×10^-15. These runs are diagnostics, not stochastic confidence evidence or attraction proofs.

Exact arithmetic reproduced low-stock surplus coefficients 369999997/15000000000, 29/280, 1/6 and 0, and additive noise coefficient 48521/20000000000000. The thermochemical floating-point pilot's maximum absolute log-identity residual was 2.5934809855243657×10^-13. The subsequent symbolic Lean proofs, not these numerical residuals, establish the identities.

No large SSA campaign or enumeration at the theorem's copy scale was run. Computations started with small boundary and algebraic tests. Lean verification ran serially in the frozen environment, with warning-as-error and no `sorry`, dependency updates or edits to packaged mathlib. Repository Python was used throughout. Failed strict receipts were retained rather than silently counted as evidence.

## Proof architecture and evidence

1. `Reservoir`, `SourceBounds`, `CountSource`, `StockNoise`, `StockExponential`, `PhaseBounds`, `RateBounds`: literal changed-source identities and local inequalities.
2. `FiniteModel` through recovery/material/phase/free/template/supply modules: stopped augmented stochastic estimates, with explicit bath state and intermediate returns.
3. `JointCounterBudget`, `PreparedCycle`, `SafeCycle`: all outputs, costs and restart failures on one joint law, with integer thresholds and the full pulse.
4. `StoppingSemantics`, `PhysicalSource` through `PhysicalNonexplosion`, `JointSourceBridge`, `JointTrajectory`: supported event identity, physical source, nonexplosion and label/wait/counter-preserving transfer.
5. `JointTimeComposition`, `LiteralCycleBound`: remove the analysis-only time boundary and identify the actual three-plus-one cycle.
6. `PhysicalHistory`, `ReturnedHistory`, `ReturnedTotals`, `FullProduct`: actual full-state conditional returns, normalized-history induction, product and linear bounds.
7. `SegmentInventory`, `PhysicalCycleInventory`, `PhysicalHistoryInventory`, `Mission`: almost-sure finite traces, net synthesis and nonempty operational mission.
8. `BathInventory`, `BathPrefixes`, `Sizing`, `InverseDesign`: exact directed prefix inventory, same-event tolerance and inverse design.
9. `Thermochemistry`, `ThermochemicalModel`, `MeteredFood`, `MissionExample`, `Resolution`: chemical accounting, metered inventory, explicit instance and consolidated root.

`TASKS.json` is the task/evidence register. `sprints/2026-09-19.md` is the running tried-and-learned ledger. `SOURCE_TRANSFER_REVIEW.md` records the structural route and why simple generated-case replay would not establish the root. The `*.verify.json` receipts distinguish successful strict closures from preserved failed attempts; failed standalone pilots can be superseded by successful root closure of their dependencies.

## AGC assessment and remaining scope

AGC was used at entry, after new structures and failures, and for the final stopping gate. Its freshness and receipt-interface checks were useful for keeping the exact source obligation visible and detecting unbound new evidence. The mathematical discoveries came from source analysis, small diagnostics and proof construction; AGC did not supply a new inequality or proof route. Proof-neutral same-frontier reconciliation was performed when requested. No generated-evidence commits, dependency changes or unauthorized theorem-graph edits were made.

The following are outside the solved scope: food-only preparation of catalytic stock; a positive net fuel-consumption lower bound; indefinite operation with finite food; passive food metering; nonideal bath activities; finite transport/contact corrections; elementary realization of the effective reverse trimolecular step; and claims of optimality for the conservative numerical constants. None is assumed by the compiled mission theorem.

Final stopping checkpoint: agc_stopping_current.json reports CURRENT after proof-neutral reconciliation. The attempted receipt publication returned AGC-POST-PROOF-E001: no synchronizable live frontier: NO_OPEN_FRONTIER. Therefore no canonical AGC theorem-graph closure/publication is claimed. This is an AGC integration limitation, not a failure of the compiled theorem. The strict root receipt, complete proof sources, task register and this handoff are the delivered mathematical evidence. No interface-repair campaign was launched after the proof was complete.

## Postproof publication delivered — 19 September 2026
Original48/48 result preserved. See POSTPROOF_HANDOFF.md for the completed24/24 publication scope, new compiled synthesis and stopped-service lemmas, exact calculator, diagnostics, and explicit remaining optional sharp joint implication. The finished paper is Reliable_Repeated_Production_Finite_Reservoirs.pdf at this workspace root; editable sources and reproduction commands are under publication/.

## Sharp refinements closed and arXiv paper delivered — 19 September 2026
The optional sharp joint implication recorded above as OPEN is now **proved**, and an independent second refinement was found. Seven new strictly verified modules (`SharpCycle`, `SharpPhase`, `SharpPhaseCycle`, `SharpEnvelope`, `SharpGeneral`, `SharpMission`, `SharpResolution`) give:

- the unrounded phase rate `kappa = 1839/8750000000000 = 2.1017142857e-10` carried through the window, burn-in, occupation and collection estimates, with a new residual-absorption lemma making `e(V) <= 101 exp(-kappa V)` hold from `V >= 1e10` instead of `2e11`, and the m-cycle mission conclusion for **every** admitted bath (`finite_bath_horizon_sharp`);
- the halved per-cycle service allowance `floor(V/10)` in the exported mission conclusion for the pure bath at `d = 1/50`, via a rebuilt sharp failure union, strict stopped-to-physical transfer, returned-history iteration and prefix sizing (`sharp_mission_bound`), hence a halved sufficient reservoir at fixed copy scale;
- certified instances `V=9.6e10, R=9.6e12, m=100, rho=1/10` at confidence 0.999979 (`sharp_example_mission`) and `V=2e11, R=2e13` at failure at most `1e-13` (`sharp_hundred_halved_bath`), plus the refined inverse design `sharp_inverse_design`.

Honest caveat carried into the paper: reducing V also reduces the guaranteed output, so a user who fixes the output demand keeps `V=2e11` and banks the gain as confidence and reservoir.

The arXiv manuscript is `key_results/RAFs/Reliable_Autocatalytic_Operation_Finite_Fuel_Waste_Bath.pdf` (25 pages); editable sources, the 92-check replay script, the figure script, the build script, the eight Lean receipts and BUILD.md are in `key_results/RAFs/Finite_Fuel_Waste_Bath_Operation_arxiv/`.
