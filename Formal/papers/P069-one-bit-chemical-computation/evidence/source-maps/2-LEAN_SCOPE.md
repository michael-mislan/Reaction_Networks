# Strictly compiled scope

Main.lean passed the frozen Lean4.30.0/mathlib environment with warningAsError=true,
exit0, no warnings, in146.297s including dependency materialization and three
declaration-interface probes. Receipt: main_verification.json. No dependency changes.

| File | What was checked |
|---|---|
| Source.lean | Literal14-channel reactants/products and falling-factorial rates; nonnegativity; zero opposing majority with<=1 minority; repair factor>=56. |
| Invariants.lean | Every enabled reaction preserves core/fuel mass; exact one-event repair update and enabling; refill food bill. |
| Partition.lean | Joint payoff equals an actual binomial-law expectation for ONE draw; complementary daughters return; n<2m impossibility. |
| UniformizationLower.lean | Finite lower-weight/lower-iterate sum is below the Poissonized kernel; monotone block iteration preserves lower bounds. |
| IntegerBounds.lean | Exponential repair bound exp(-56)<=10^-6; exact error-budget and ten-cycle arithmetic; natural quotient downward bound and concrete overflow inequalities. |
| ConcreteWitness.lean | Literal source repair-clock bound for gamma>=10^9 and x>=8,y=1,h=1; corrected pure inventory. |
| Iteration.lean | Conditional-success recurrence implies q^n, without independent cycles. |
| Main.lean | Imports all modules, combines exact arithmetic and prints decisive theorem axioms. |

Printed decisive axioms are only Classical.choice, Quot.sound and propext. No sorry
or native_decide evaluation axiom occurs in those declarations. Three elaborated
declaration interfaces are saved in the strict receipt.

## What is conventional/exact-computational rather than K

The concrete3240-state recurrence result is reproduced with checked64-bit integer
arithmetic in Python; its entire execution is NOT replayed by Lean. The concrete
weight lower bounds, source-to-semigroup interpretation, full CTMC common-clock
coupling, Markov conditioning at tau, and identification of actual multi-cycle event
probabilities with the recurrence are conventional bridges in TECHNICAL_NOTE.md.
The generic Lean lemmas have explicit premises; none is presented as discharging
these bridges automatically. certified_arithmetic_margin proves arithmetic about
the reported numerator, not that the numerator is the source probability.

F6 uses the guide's alternative 'decisive new theorem instance': literal_repair_clock
and corrected_inventory. It does NOT mean a kernel-checked full finite certificate.
This completes the guide's modular formalization scope alongside the C/E theorem;
it does not meet the alternative stopping criterion of an end-to-end Lean solution.
