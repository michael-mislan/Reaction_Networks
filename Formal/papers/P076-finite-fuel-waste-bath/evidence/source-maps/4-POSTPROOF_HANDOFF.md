# Publication handoff — 19 September 2026

> **Addendum, same day: the optional sharp joint node is now CLOSED, and a second
> refinement was found and propagated.** See `CLAIM_EVIDENCE.md` and
> `../../key_results/RAFs/Finite_Fuel_Waste_Bath_Operation_arxiv/BUILD.md`.
> Seven new strictly verified modules under `proofs/FiniteReservoir/`:
> `SharpCycle`, `SharpPhase`, `SharpPhaseCycle`, `SharpEnvelope`, `SharpGeneral`,
> `SharpMission`, `SharpResolution` (receipts in this workspace and copied into
> the paper package). Results: (i) the phase exponent is
> `kappa = 1839/8750000000000 = 2.1017e-10`, not the printed `1e-10`, and a new
> absorption lemma makes `e(V) <= 101 exp(-kappa V)` valid from `V >= 1e10`
> rather than `2e11`; (ii) the halved per-cycle allowance `floor(V/10)` now
> appears in the **exported** mission conclusion for the pure bath at `d=1/50`,
> so the sufficient reservoir halves at fixed `V`. The 100-cycle instance at
> confidence 0.999979 is matched at `V=9.6e10, R=9.6e12`; at the original
> `V=2e11` the same mission has failure at most `1e-13` with `R=2e13`. The
> statements below about the open node describe the position *before* that work
> and are retained as the record of why it was deferred.

Original campaign: **48/48 PASS**. Postproof publication deliverables: **24/24 PASS**, using the guide's explicit allowance to complete an optional investigation while retaining the established constants. The optional sharp **joint** mission remains red; completion of the publication register does not claim that stronger theorem.

## Delivered paper

`Reliable_Repeated_Production_Finite_Reservoirs.pdf` is saved at this workspace root. It is a 19-page research manuscript with a self-contained model, quantified main theorem, critical proof narrative, explicit error budget, same-event synthesis, inverse/fixed-budget design, finite-bath thermochemistry, worked dimensions, three scientific figures, evidence boundaries and reproducibility appendix. It follows the original compiled joint theorem and its immediate established consequences. Discovery detours and the undocked sharper-service proposal are kept out of the proof narrative.

Editable sources are under `publication/`, beginning with `paper.tex`. The model, theorem, proof, corollaries, thermochemistry, examples, quantitative appendix, reproduction map and bibliography are separate files. `publication/README.md` provides exact commands; `publication/build.py` rebuilds and copies the PDF to this root. `publication/QA.md` records the render-and-inspect pass. `publication/manifest.json` identifies actual source and receipt hashes, including working-tree additions.

## What improved

**Terminal stock is now credited in the actual finite-bath trace.** The compiled `ProductionCorollaries.lean` establishes

    S_net >= m ceil(V/56) + ceil(V/28) - I_initial.

It derives the integer uniform bound subtracting floor(161V/160), the real bound `[(m+2)/56-161/160]V`, positivity for m>=55, and the all-free 100-cycle value **164285714343**. These are properties of the existing joint success event and cost no probability. The proof uses the actual FiniteReservoir history, exact inventory telescoping, nonnegative removed templates and the fact that pulses add only food. The finite-bath trace has not been replaced by C2's maintained-bath law.

**The proposed service improvement survives at the actual stopped-source level.** `SharpService.lean` proves the correlated gross-intensity envelope 11V/500 for M=R,d=1/50 and an exponential bound for the full three-stage stopped count source at threshold V/10-1. The exponent margin is 21/31250, sufficient for the old exp(-V/2000) error allocation even with the integer buffer when V>=1e6. Strict verification passes with empty diagnostics.

**Mission calculations and physical interpretation are executable.** The calculator evaluates only original-theorem formulas, returning exact output counts, preparation-inclusive food allocations, confidence, gross allowance, activity corridor and evidence status. High-precision logarithms select a candidate; positive rational Taylor sums certify the confidence inequality. Extreme-confidence inputs use bounded bracketing/bisection, and displayed confidence is rounded downward exactly. Insufficient stocks and invalid horizons are handled explicitly.

**Endpoint energies are explicit.** Conventional algebra from the compiled factorial potential yields, for pure fuel, `Delta G_b=-A0 J-log binom(R,J)` and for loaded fuel/waste, `Delta G_b=-A0 J+log[(R-J)!(R+J)!/(R!)²]`, with A0=log(80000000000). Supported endpoints including zero waste are finite. Bath free-energy decrease is distinguished from useful work and apparatus entropy production.

## What stayed at the original constants, and why

The certified paper example retains **V=200000000000, R=40000000000000, m=100, rho=0.1**, confidence at least **0.999979**, template collection **357142857200**, and free-X collection **18518518600**. Food is at most 10^14 molecules of each species during operation; preparation is separately charged. The two outputs overlap.

The stopped-tail refinement is not yet a complete sharper joint event. Existing exported success predicates fix floor(V/5) through prepared success, strict physical transfer, literal-cycle success, returned-history iteration and prefix sizing. The exact missing result is a uniform actual literal-cycle joint lower bound with both outputs, both food budgets, restart and `G<=floor(V/10)`, followed by history composition and sharp prefix summation. Merely altering a definition or passing a stronger local inequality into a theorem whose conclusion still says V/5 does not prove it.

The first independent-cap calculation was too weak; the corrected correlated calculation is mathematically sound and compiled. The remaining issue is the stronger source-to-history interface, not a corridor mismatch or failed exponential inequality. In accordance with the guide's publication endpoint, this larger optional propagation was not allowed to delay the paper. **R=20000000000000 and 33.2108 nL are not certified joint mission values.** The calculator does not offer them. `POSTPROOF_GRAPH.json` decomposes the remaining red node into source identity (green), inequality (green), joint stopping/conditioning bridge (red), and instantiated prefix/sizing corollary (red).

## Tests, failures and lessons

The canonical Python environment and native numerical smoke suite passed. Computations were small: 102 exact rational corridor/bath checks, 670 endpoint energy checks including boundaries, and four eight-cycle ODE runs. The endpoint numerical residual was at most about 1.71e-13; the conventional factorial algebra supplies the proof. Lean compilation was serial and used the frozen repository toolchain, warnings-as-errors, without sorry or dependency updates.

The initial sharp Lean pilots failed on unused-variable and unnecessary/unreachable tactic lint errors. Removing the unused premise and simplifying the proof script closed these errors without changing the mathematical model. Failed receipts were preserved by the verification bridge. A high-demand calculator pilot exposed excessive Fraction repeated-squaring cost; interruption and a bounded positive Taylor sum removed it. An extreme failure target 10^-100 now also passes without catastrophic cancellation or count-by-count search.

New deterministic runs at r=20 compare pure and loaded baths with R/V=1,d=.02; nearly depleted pure fuel with R/V=.001; and zero drive. Minimum per-cycle QI/V was about .275215, .275215, .277266 and .278579 respectively. The nearly depleted bath ended at a_F about 2.37334e-10; zero drive had identically zero directed service. All forward, reverse, net and gross fluxes, both outputs, final internal inventory and sampled prefix extrema are separately saved. The six original runs retain their original parameters and provenance under `experiments/finite_bath_results.json`.

These comparisons support the interpretation that operation, activity tolerance and positive net fuel consumption are distinct questions. They do not certify stochastic confidence, a pathwise occupancy lower bound or an attractor. A positive net-service theorem would require the missing occupancy and directed-tail argument; it is not a gate for this publication and is not assumed.

The worked dimensionalization chooses both reference concentrations as 1 mM and the time unit as 60 seconds. It gives reactor volume about .332108 nL, original bath volume 66.4216 nL and 400 minutes of source-running time. The rate-units table makes that convention explicit. No calibrated chemistry, medical application, passive-food model or autonomous infinite operation is claimed.

## AGC and evidence

AGC checkpoints were run at entry, new structure/failure review, prepublication and final handoff. The final checkpoint reports **CURRENT**, with classification `current_with_unbound_authored_route`. This is useful for scope/freshness, but its canonical cut is not a substitute for the completed root receipt and it provided no new mathematical inequality. The known `NO_OPEN_FRONTIER` canonical publication limit remains recorded. No AGC integration repair, theorem-graph publication or generated-evidence commit is claimed.

`Resolution.verify.json`, `ProductionCorollaries.verify.json` and `SharpService.verify.json` each report verified=true, exit code zero and empty compiler diagnostics. Their proof hashes match the delivered files. `CLAIM_EVIDENCE.md` is the short status map; `POSTPROOF_NOTES.md` contains the full investigation record; `sprints/2026-09-19.md` preserves numbered timestamped entries. No necessary implication remains open for the original mission or the publication scope. The optional sharper joint theorem remains explicitly open, and the paper is ready for scientific authorship/editorial decisions without representing that refinement as solved.
