# Publication theorem index

All source paths are relative to the repository root. Existing descriptive declarations are retained as public names; no duplicate aliases are necessary.

| Paper role | Declaration | Source |
|---|---|---|
| Main theorem | `SparseLinearRAF.sparse_linear_raf_literature_resolution` | `proofs/SparseLinearRAF/LiteratureResolution.lean` |
| Negation of high-probability linear assertion | `SparseLinearRAF.no_high_probability_linear_raf` | same |
| Saturated productive extraction | `SparseLinearRAF.saturated_support_extraction` | `proofs/SparseLinearRAF/SaturatedProgram.lean` |
| Unique acyclic decoder and assignment encoding | `AssemblyCode`, `ProgramEncoding` modules | `proofs/SparseLinearRAF/AssemblyCode.lean`, `ProgramEncoding.lean` |
| Factorial support count | `SparseLinearRAF.support_count_mul_factorial_le` | `proofs/SparseLinearRAF/SupportCounting.lean` |
| Bounded-rank disappearance | `SparseLinearRAF.bounded_cover_rank_probability_tendsto_zero` | `proofs/SparseLinearRAF/BoundedRank.lean` |
| Single catalyst, both orientations | `SparseLinearRAF.single_catalyst_probability_tendsto_zero` | `proofs/SparseLinearRAF/SelfConstructionLimit.lean` |
| Minimum RAF size, infinity if none | `SparseLinearRAF.minimum_raf_size_superlinear` | `proofs/SparseLinearRAF/PublicationConsequences.lean` |
| Minimum catalyst rank | `SparseLinearRAF.minimum_catalyst_rank_diverges` | same |
| Conditional disappearance | `SparseLinearRAF.linear_raf_conditional_vanishes`, `SparseLinearRAF.bounded_rank_conditional_vanishes` | same |
| Abstract window combination | `SparseLinearRAF.size_window_lower_bound` | same |
| Quantitative bound, strictly verified | `SparseLinearRAF.linear_raf_quantitative_bound` | `proofs/SparseLinearRAF/Quantitative.lean` |

The positive quadratic witness theorem is cited from Hordijk and Steel (2016), Corollary 2; it is not represented as locally formalized. Conditional declarations accept an eventual positive lower bound on the conditioning probability. The application to RAF existence uses the inclusion of the small-RAF/bounded-rank event in RAF existence. A liminf lower bound delta>0 supplies an eventual bound delta/2.

## Final publication audit

`PublicationAudit.verify.json` strictly exports all twelve listed public results (paired conditional declarations count separately). It reports verified=true, exit_code=0, empty stdout/stderr, and warnings-as-errors. All twelve axiom profiles are exactly Classical.choice, Quot.sound, propext. The audit completed in 348.703 seconds with 52 authenticated local dependencies. The root source was not changed.

Paper numbering: active-cover bound 2; saturated extraction 3; fixed-depth bound 4; bounded-rank theorem 5; factorial support count 6; linear support entropy 7; uniform large-rank bound 8; quantitative corollary 9; minima 10; conditional corollary 11; cited-input size window 12. Theorem 1 is the root.

`PolynomialIntensityAudit.lean` is outside `PublicationAudit` and outside the paper. Its two scalar input lemmas do not constitute a growing-intensity RAF theorem.
