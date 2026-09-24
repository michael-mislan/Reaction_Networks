# Exponential-rate investigation

The question is source-specific: at fixed positive confidence, what is the
infimum asymptotic rate of log M_K / K allowing the specified all-prefix
positive-count enrichment event, when molecular scale and finite service
allowances may increase? The existing necessary count ceiling is not a matching
converse for this stochastic source. The source, event, and allowed parameter
sequences must remain fixed in any optimality claim.

## Test 1: Is exp(g) the likely optimum?

The 40-cycle constant-rate comparison in postproof_pilot.py keeps the exact
fourfold total-size stopping rule. It integrates H=H0 exp(aH s),
L=L0 exp(aL s), with proportional transfer and the stationary source rates.
The minority dilution factor approaches 4^(1-aL/aH)=2.51553657525, whereas
exp(g)=2.12499889432. This tests a reduced deterministic model only; it does
not simulate the finite source or establish a stochastic asymptotic theorem.

The discrepancy is structural. With H dominant, the operational batch time
approaches log(4)/aH and minority size grows by 4^(aL/aH). Hence its share
decays at rate lambda=log(4)(1-aL/aH). A lower bound on selection gain g does
not force this actual decay to be only g. Calling exp(g) attainable would be
unjustified even in this reduced model.

## Testable route 2: minority-growth exponential barrier

At safe source rates aH<=3 and aL>=.99, consider
V=exp[(N/1000)(eta log W-log L)], with eta=.32.
The discrete logarithm inequalities already checked in PopulationLogBounds
give a linear drift at most (N/1000)(3 eta-.99*.999)
=-.00002901 N. The existing exponential-jump remainder scale is at most
6N/390625=.00001536 N. There is a strict remaining negative margin.
This discrete scalar exponential-generator inequality has now compiled in
`proofs/SerialTransferSelection/MinorityGrowthBarrier.lean`, declaration
`SerialTransferSelection.minority_growth_scalar_barrier`; the strict receipt
is `verification/minority_barrier.json`. It uses only the standard three Lean
axioms and no numerical oracle. It is not yet a source endpoint or iterated
probability theorem.

If a corresponding endpoint bound log(L/L0)>=eta log4-a is connected to the
original law, the share base becomes 4^(1-eta) exp(a)(1+epsilon)/(1-epsilon).
This changes the exponential rate, unlike the retired normalization correction.
It must be accompanied by the new barrier failure probability in every cycle.

## What a sharp source theorem would additionally require

A matching result near log4(1-zL/zH) needs quantitative shrinking-neighborhood
chemical tracking (including the finite gamma dilution correction), a uniform
long-horizon comparison through the minority regime, and a converse controlling
minority survival below that population scale. Neither a pointwise drift bound
nor a deterministic limiting calculation supplies these implications. The
fixed source has actual heterogeneous division phases and intact-cell transfer;
they cannot be replaced by independent molecular sampling. At every stage,
failure mass must remain in the original finite marked law.

No optimal exponential constant is currently proved. The requested attempt
yielded both a discriminating finite-model calculation and a checked new
barrier, but it did not close the full source implication or its converse.
This investigation is
kept separate from the publication's proved critical path until an improved
source-level mission theorem is available.
