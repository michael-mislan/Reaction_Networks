import proofs.RandomViability.BindingCompetitionConsequences
import proofs.RandomViability.BindingCompetitionTimedComparison
import proofs.RandomViability.BindingCompetitionSizing

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

/-- Duration-specific supplies with the convenient exponential confidence bound. -/
theorem competition_publication_probability (V : ℕ) (s : ℝ≥0) (m : ℕ)
    (p : CompetitionRateBox) (hV : 100000000 ≤ V) (hv : 0 < (V:ℝ))
    (hH : (m:ℝ)+(s:ℝ) ≤ competitionDuration V) :
    1-2*Real.exp (-(2/100000000)*(V:ℝ)) ≤
      competitionTimedFullExpectation V s m p hv
        (FiniteKernel.eventIndicator {X | competitionTimedFullGood V s m X}) := by
  have hh := competition_timed_supplied_probability V s m p hv
  have he := competition_timed_error_bound V s m hV hH
  linarith

end
end RandomViability.Binding
