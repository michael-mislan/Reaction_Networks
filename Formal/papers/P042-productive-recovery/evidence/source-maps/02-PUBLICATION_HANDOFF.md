# Publication handoff: productive recovery and repeated harvesting

## Delivered result

The publication is `Productive_Recovery_and_Repeated_Harvesting.pdf` in this workspace root. Its companion LaTeX source has the same stem. The paper presents the final strengthened critical proof path: source and pulse, material relaxation, the 1/20 guard, actual conditioning and routine return, aggregate and free-X export, resource budgets, repeated operation and net synthesis. Discovery-only lemmas and compiler history are excluded from the paper.

Original C1 remains **49/49 PASS**. The separate postproof register records the 24 requested items and their individual evidence categories. The original proof files and original completed theorem were not rewritten. Added proof modules use the same frozen Lean 4.30.0 and mathlib environment.

The new assembled declaration is `ProductiveRecovery.conditioned_productive_operation`, in `proofs/ProductiveRecovery/PostproofResolution.lean`. Its strict receipt is `verification/PostproofResolution.verify.json`: exit0, empty compiler stdout/stderr, warnings treated as errors, five exported declaration interfaces, 36 current local dependency sources/artifacts. Its exported interfaces report only propext, Classical.choice and Quot.sound. The final publication audit also checks the earlier original and intermediate successful receipts against current source hashes. No new axiom, sorry, native_decide certificate or warning suppression was introduced.

## Exact strengthened scope

Keep one fixed r in [19,21] and delta in [1/50,1/25]. Food inputs and all washout rates are one. F/P activities are maintained at one. The source has six internal coordinates and the six reversible pairs shown in the manuscript. Source correspondence and fixed compatible thermochemistry are inherited from the original C1/C0 developments.

The pulse retains q in [1/4,3/4] of the well-mixed state, applies species-specific retention multipliers in [49/50,1], and adds only foods 1-q+eU and 1-q+eW with errors in [-1/200,1/200]. It is an ideal instantaneous externally operated pulse.

From the original admitted region (nonnegative, A,B in [.9,1.1], Y>=1/5000), one pulse and12 time units produce the stronger returned region B* (nonnegative, A,B in [159/160,161/160], Y>=1/20). Routine cycles start from that actual returned state. After each routine pulse, Y>=1/20 at every time>=5/2, and the state is in B* at every time>=3. Collection is[3,4], followed by the next pulse on the actual time4 endpoint.

Each routine cycle guarantees:

- Template-equivalent measured output >=1/28.
- Free-X concentration >=1/540 on[3,4], and its measured export >=1/540.
- Each food addition, including pulse, <=951/200.
- Gross forward-plus-reverse driven service <=9/50.
- Returned endpoint in B*.

Conditioning allowances are each food<=2551/200 and gross service<=27/50. Conditioning plus any m routine cycles has template output>=m/28, each food<=(2551+951m)/200 and gross service<=(27+9m)/50. On the same concatenation, net synthesis integral(j0+j3-j5)>=m/28-11/10. The guarantee becomes positive at m=31 and grows thereafter.

The root allows an arbitrary state-dependent intervention protocol, not merely a preselected constant pulse. The source parameters remain fixed. It constructs conditioning and routine trajectories, verifies derivative equations and nonnegativity, and links each endpoint to the next starting state. Uniqueness remains available through the original `actual_return_unique`. The stronger all-later-times return assertions are separately exported in the current `StrongReturn` receipt.

## What was tested and learned

### 1. Larger source growth region

Exact rational arithmetic confirmed the parameterized drift inequality supplied in the assessment. At beta=1/20, the surpluses after subtracting(2/3)Y are x:4999999991/45000000000, c1:51/280, c2:1/6, and z:at least0. The calculation was then bound to the literal source and compiled as `parameterized_drift` and `strong_guarded_growth`.

The key insight is quantitative: the old tiny guard was not imposed by the chemistry. The same food-sequestration inequalities permit a substantially larger working stock. There is no need to optimize weights or find a global attractor. The zero z-surplus does not prevent positive drift at the target boundary.

### 2. Conditioning is different from routine recovery

The retained stock is at least49/200 of the pre-pulse Y. Initial conditioning starts from49/1000000; routine recovery starts from49/4000. Exact Taylor bounds prove exp(36/5)>50000/49 and exp(3/2)>200/49. A generic strict exponential fence with rate3/5, below the source rate2/3, proves the endpoints. Exact material relaxation and exp3>16 establish the material deadline3.

This separates the one-time investment in catalytic stock from its subsequent replenishment. Relative to the original theorem, the measured-window lower bound improves125-fold, and the certified average measured amount changes from1/17500 to1/112 per normalized time. These comparisons are recorded here; the paper develops the strongest result without carrying the obsolete constants through its proof.

The general retained-stock design law is proved conventionally in the manuscript: allowance max(0,log(beta/(alpha*b))/gamma), with a separate material deadline. This is sufficient, not necessary. The fixed-target strict fence used for the actual deadlines is compiled.

### 3. Free-X output

Direct source inequalities bound all four catalytic phase losses by70, retaining the productive links20,20,20 and38. Three scalar integrating-factor comparisons give the polynomial transfer bound with coefficient580 for c2. At delay1/35, coefficient comparison and exp2<9 yield x(t+1/35)>=Y(t)/27. Since catalytic recovery precedes collection by more than this delay, free-X export is positive uniformly.

The useful mechanism is not an assumption that aggregate stock is already free product: the actual reactions release X. The source inequalities, phase transfer, delayed free-X floor and collected free-X bound all compile. The proof avoids a matrix-exponential library or phase-by-phase numerical certification.

### 4. Synthesis beyond the initial load

The integrated identity I'=j0+j3-j5-I was extended to arbitrary nonnegative segment duration. Pulse withdrawals and additional losses were included before telescoping. Measured output is a subset of continuous export. Nonnegativity and I_initial<=A_initial<=11/10 then prove the cumulative net-synthesis bound.

This closes the initial-stock interpretation gap. The result concerns source-defined template equivalents, while actual elemental material enters through food. A separate optional bound isolating cumulative net j3 was not added: it is not necessary for the requested net-synthesis result or the paper's critical path.

### 5. Targeted numerical diagnostics

`experiments/postproof_pilot.py` uses the literal source, Radau, rtol1e-9, atol1e-12, and no coordinate clipping. The guarded120-second run completed in42.204 seconds using the canonical repository Python; the numerical environment smoke test passed before it.

The experiment covered96 conditioning trials and96 routine trials. Each set combines all four parameter corners, four pure plus two mixed catalytic compositions, q=.25/.75, and uniform versus species-dependent losses. Food error was adverse in all recovery trials. Conditioning used A=B=.9, Y=.0002. Routine trials used the valid strong starting material boundary A=B=159/160 and Y=.05.

The largest computed hitting times were5.6731960062 (conditioning) and1.2258254874 (routine). Both occurred for pure C2, r19,delta.04,q.25,uniform loss. No proposed deadline, returned-state or routine-output bound failed. These are sample diagnostics, not uniform enclosures. Their constants are supported by the compiled inequalities independently of the simulations.

Eight varying-intervention cycles at each parameter corner added32 segments. Retention cycled through .25,.75,.4,.6; losses alternated between the two patterns; refill errors alternated signs. The maximum integrated inventory residual over all224 segments was5.77316e-15. The balance is a linear invariant accumulated within the same solver, so this measures implementation consistency and is not independent evidence of integration accuracy. The figure and manuscript make that limit explicit.

### 6. Compiler diagnostics and route decisions

No mathematical proposal in the postproof critical path was falsified. The failed attempts were implementation issues:

- A first helper invocation used the Windows default text encoding; rerunning canonical Python with `-X utf8` fixed Unicode Lean source handling.
- Source product nonnegativity required explicit coordinate hypotheses rather than an automatic positivity inference.
- Derivative algebra required reducing `id t` before polynomial normalization.
- Two unnecessary tactic sequencing constructs were rejected by the strict linter and removed; no linter was disabled.
- Shifting a vector-valued trajectory required the scalar-to-vector chain rule `HasDerivAt.scomp`, rather than scalar-output `comp`.
- A generated time generalization initially replaced a flux coordinate index along with the time endpoint; the source index was restored to5 before verification.

The final root receipt is authoritative. Earlier failed module receipts and console files remain historical diagnostics; they do not override later strict compilation of those modules in the root dependency closure. No broad original proof replay or dependency update was needed.

## Conventional consequences and physical interpretation

The paper proves conventionally that B* is nonempty, compact and convex, and that the fixed-intervention return map is continuous. A common compact trajectory bound plus polynomial local Lipschitzness gives continuous dependence. Brouwer then gives a productive periodic hybrid state. This auxiliary corollary is explicitly conventional, not claimed as Lean-compiled; it asserts no attraction or uniqueness of the periodic state.

The dimensioned example uses1mM,60seconds,1mL. Routine operation is3minutes recovery plus1minute collection, at least35.714nmol template equivalents and1.85185nmol freeX, each food at most4.755micromol, and gross service at most.180micromol. Initial stock and conditioning supplies are separate. The conversion rule is kdim=kmodel/(tau*cstar^(p-1)), with consistent reservoir activity conventions.

The manuscript states the physical limitations prominently: schematic balanced species, no molecular calibration, an effective reverse three-reactant channel, maintained external F/P activities, zero-duration idealized pulses, mixed effluent, and service distinct from total apparatus work. It cites Rao and Esposito's primary open-network thermodynamics paper, whose publication information was checked directly.

`C2_HANDOFF.md` names exact inherited source/count marks, nested deterministic regions and slack, an optional conventional intermediate entry-band calculation, and the remaining actual finite-copy kernel and joint-law obligations. No stochastic probability has been inferred from deterministic simulation or recovery. Finite baths, attraction, purification and laboratory construction remain outside this task.

## Publication package and visual review

- `Productive_Recovery_and_Repeated_Harvesting.pdf`: final12-page paper in workspace root.
- Matching `.tex`: publication source, with complete source-specific argument and formal correspondence appendix.
- `figures/`: four vector PDF figures; `build_figures.py` reproduces them from saved numerical data.
- `build_paper.ps1`: two LaTeX passes with failure checking.
- `reproduce.ps1`: environment checks, strict theorem verification, guarded numerical diagnostics, figures and paper.
- `verification/publication_audit.json`: current proof/dependency hashes, allowed axioms, preserved original completion and artifact hashes.
- `POSTPROOF_TASKS.json`, `POSTPROOF_STATUS.md`, daily sprint ledger and hypothesis graph: separate postproof progress and evidence categories.

The installed LaTeX toolchain was used because canonical repository Python lacked reportlab; no package lock or numerical environment was changed. The PDF was rendered with Poppler and every page inspected. Inspection found a long unbreakable path and a plot legend overlapping bars; the path formatting and plot limits were corrected. The final build has zero overfull boxes and no unresolved references. MiKTeX printed its general update-check notice; no update was run or required for the successful build.

## AGC and final boundary

AGC checkpoints were run at entry, new-structure and phase gates, compiler-failure/recovery gates, and publication handoff. When a checkpoint identified newly written evidence as unconsumed, its exact same-cut `authority reconcile-frontier` command was followed by another checkpoint. This was proof-neutral and did not change theorem status.

AGC was useful for detecting freshness changes and retaining the newly authored focus. Its initial mathematical recommendation still described the already-completed original source/return route; it did not supply the new growth, phase-transfer or synthesis arguments. Strict Lean receipts, not AGC freshness or numerical output, establish the compiled claims. Final stopping concerns the requested postproof work and publication; C2 remains a separate unresolved probability problem.
