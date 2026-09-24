# Printed claims and evidence scope

Strict module: `proofs/BiochemicalReadout.lean`, Lean 4.30.0, warning-as-error, exit 0, empty stdout/stderr. Saved receipt: `evidence/BiochemicalReadout.verify.json`. Proof SHA-256: `6b72e6f54b3f229973b3359b3ca8f08f16173b74ed0cbeca702dd3f14d24a504`. Frozen lake manifest SHA-256: `a8df0b606ec258561c226df89856884be433c19b49fb0a27335d69bb2b6e9fac`. No dependencies outside Mathlib are imported.

| Printed result | Declaration / evidence | Boundary |
|---|---|---|
| Literal free/complex field subtraction | `source_deficit_identity`, `stored_deficit_identity` | Algebra on explicit fields, no existence claim |
| Finite integrated account, Proposition 2 | `finite_account` | FTC from continuous trajectories and stated derivative; source substitution supplied by identity |
| Complete-recovery cost factor | `turnover_cost` | Exact algebra; convergence and integrability proved conventionally in paper |
| Finite recovery remainder | `recovery_remainder` | Algebra from integrated recovery equation; exponential and tail comparison conventional |
| Native/background ambiguity | `merged_source`, `alias_fluxes`, `equal_law_error` | Source and probability arithmetic; ODE uniqueness and common noise kernel argument conventional |
| Guide seed window | `seed_window` | Exact supplied rational margin; source comparison conventional |
| Theorem 1 kinetic/preparation certificate | `parameter_certificate`, `preparation_preservation` | Exact arithmetic and envelope transport |
| Theorem 1 threshold | `decision_certificate`, `joint_protocol` | Exact classifier implication assuming the source envelopes |
| Source envelopes, Proposition 3 | Paper complete integrating-factor proof | Conventional, not claimed Lean compiled |
| Global physical domain | Paper inward-face and bounded ODE proof | Conventional |
| Finite uniform tail | Paper exponential-convolution proof; exact Taylor preflight in `experiment.py` | Conventional analysis, exact Python arithmetic support; not Lean exponential proof |
| Continuum theorem | Propositions 2 and 3 plus exact rational certificate | Mixed conventional + formal evidence; numerical draws do not prove continuum coverage |
| Numerical tables and figure | `experiment.py`, `results.json`, `figures/design.pdf` | Deterministic ODE evidence, not biological data |
| Biochemical architecture | `LITERATURE.md`, `APPLICATION.md` | Component directions literature-supported; combined implementation/calibration prospective |

The first compile failed because a scalar multiple of an FTC equality was not supplied to the arithmetic tactic and an unnecessary hypothesis triggered the strict unused-variable warning. These were representation failures, not counterexamples. The saved failed attempt remains under `evidence/`; the stable proof file was fixed in place. No warning or failed receipt was counted as proof.

No claim that this is a fully Lean-formalized solution of a named open conjecture is made. The attached guide explicitly allows complete conventional source proofs with proportionate compiled support. That is the selected completion route.

## Second module (added 17 September 2026 for the arXiv package)

Strict module: `proofs/BiochemicalReadoutExtensions.lean`, namespace
`BiochemicalReadout.Ext`, Lean 4.30.0, warning-as-error, exit 0, empty
stdout/stderr, 27.7 s. Source SHA-256:
`16015cde419dc8dc07464d2e8d975c94ff4a91014cd0f627ed730c7b880f052b`. Receipt:
`key_results/RAFs/Biochemical_Readouts_Native_Function_arxiv/verification/BiochemicalReadoutExtensions.verify.json`.
Probed roots `fading_recovery_tail`, `ideal_recovery_tail`, `slope_sandwich`
each depend only on `propext`, `Classical.choice`, `Quot.sound`.

| Printed result | Declaration | Boundary |
|---|---|---|
| Both forms of the outstanding loss, incl. residual association mass | `remainder_forms`, `residual_remainder` | Algebra; convergence conventional |
| Divided-slope sandwich for nonlinear kinetics | `slope_sandwich` | Division-free inequalities from the integral balances |
| `exp(9.65) > 14000` from a Taylor partial sum | `exp_965_gt`, `exp_neg_965_lt` | Real-exponential statement, not a rational surrogate |
| Ideal-switch recovery remainder `< 3e-6` | `ideal_recovery_tail` | Uses `Real.exp`; the envelopes are conventional premises |
| Fading-switch remainder `< 4e-6` at `gamma >= 21`, `tau = 5` | `fading_recovery_tail` | Same; the sharper `2.4e-6` is exact rational arithmetic in `check_paper.py` |
| Additional complete loss at `gamma = 21` | `fading_extra_loss` | Two-sided rational bound |
| Absolute preservation envelopes, class flux separation | `absolute_envelopes`, `class_flux_bounds` | Exact rational |
| Set-inversion endpoints and flux monotonicity | `outer_upper`, `outer_lower`, `flux_monotone` | Algebra behind the continuous outer sets |

`slope_sandwich` is stated without division, so it needs neither `0 < I` nor
`0 <= W`; both hypotheses were removed after the strict linter flagged them as
unused.
