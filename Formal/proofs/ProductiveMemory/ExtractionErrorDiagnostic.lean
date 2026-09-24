import proofs.ProductiveMemory.ExtractionParameters

namespace ProductiveMemory
open FiniteCopy
noncomputable section
set_option Elab.async false

/-- The remainder of the certified failure budget is at most three parts per million.
This is a bound decomposition, not a claim about observed failure frequencies. -/
theorem productive_nontransfer_error (p : ℝ) :
    productiveCycleError recoveryCount productiveM productiveTime p (1/50)-
      32/((1/50:ℝ)^2*p*(productiveM:ℝ)) ≤ 3/1000000 := by
  have h := productive_cycle_error_evaluated (1/100) le_rfl
  have he : productiveCycleError recoveryCount productiveM productiveTime p (1/50)-
      32/((1/50:ℝ)^2*p*(productiveM:ℝ)) =
      productiveCycleError recoveryCount productiveM productiveTime (1/100) (1/50)-1/500 := by
    unfold productiveCycleError
    norm_num [productiveM]
    ring
  rw [he]
  linarith only [h]

theorem productive_transfer_error_at_floor :
    32/((1/50:ℝ)^2*(1/100)*(productiveM:ℝ))=1/500 := by norm_num [productiveM]

end
end ProductiveMemory
