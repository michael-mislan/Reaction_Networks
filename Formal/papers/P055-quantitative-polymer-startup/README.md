# Reliable finite-time output from stochastic autocatalytic reactors: retained rewards, uncertain background catalysis, and quantitative startup

[Read the paper](../../../Theory/Production/P055-quantitative-polymer-startup.pdf) · [Manuscript](manuscript/main.tex) · [Claim map](claims.json) · [Build instructions](../../BUILD.md)

Retained rewards convert autocatalytic availability into finite-time stock and output guarantees under uncertain background catalysis. The paper gives joint mission and all-window output bounds, food budgets, and quantitative startup scales.

**Formalization:** The background-robust stochastic mission theorem and its all-window extension are conventional proofs. The food-silent mission and selected rounding, drift, variance, and error-budget components are formalized.

Selected Lean sources:

- [Resolution.lean](../../proofs/StartupMarked/Resolution.lean)
- [ParameterizedFloor.lean](../../proofs/StartupCount/ParameterizedFloor.lean)
- [RobustSharpening.lean](../../proofs/StartupCount/RobustSharpening.lean)

[Verification scope](../../VERIFICATION.md) · [All papers](../../../README.md)
