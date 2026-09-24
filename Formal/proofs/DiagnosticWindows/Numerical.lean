import proofs.DiagnosticWindows.Instance
import proofs.DiagnosticWindows.ExpCertificates

namespace DiagnosticWindows

theorem blankSum10_bound : 99/100 ≤ blankSum10 := by
  have h0 := exp_capacity10_0
  have h1 := exp_capacity10_1
  have h2 := exp_capacity10_2
  have h3 := exp_capacity10_3
  have h4 := exp_capacity10_4
  unfold blankSum10
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]

theorem targetSum10_bound : targetSum10 ≤ 27/10 := by
  have h0 := exp_capacity10_0
  have h1 := exp_capacity10_1
  have h2 := exp_capacity10_2
  have h3 := exp_capacity10_3
  have h4 := exp_capacity10_4
  unfold targetSum10
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]

theorem blankSum5_bound : blankSum5 < 99/100 := by
  have h0 := exp_capacity5_0
  have h1 := exp_capacity5_1
  have h2 := exp_capacity5_2
  have h3 := exp_capacity5_3
  have h4 := exp_capacity5_4
  unfold blankSum5
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]

theorem targetSum5_bound : 7/2 < targetSum5 := by
  have h0 := exp_capacity5_0
  have h1 := exp_capacity5_1
  have h2 := exp_capacity5_2
  have h3 := exp_capacity5_3
  have h4 := exp_capacity5_4
  unfold targetSum5
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]

theorem capacity10_errors : blank10 (16/5) ≤ 1/100 ∧ miss10 (16/5) ≤ 1/20 := by
  constructor
  · rw [blank10_exact]; linarith [blankSum10_bound]
  · rw [miss10_exact]
    have h := mul_le_mul_of_nonneg_left targetSum10_bound (Real.exp_pos (-4)).le
    have he := exp_loading.2
    nlinarith

theorem capacity5_separating_errors : 1/100 < blank5 5 ∧ 1/20 < miss5 5 := by
  constructor
  · rw [blank5_exact]; linarith [blankSum5_bound]
  · rw [miss5_exact]
    have h := mul_lt_mul_of_pos_left targetSum5_bound (Real.exp_pos (-4))
    have he := exp_loading.1
    nlinarith

end DiagnosticWindows
