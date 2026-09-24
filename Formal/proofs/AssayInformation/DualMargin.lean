import proofs.AssayInformation.RescueCertificates

set_option maxRecDepth 8192
noncomputable section
namespace AssayInformation
open DiagnosticWindows
open scoped BigOperators

theorem dual_exp_0 : (19215788783/20000000000) ≤ Real.exp (-1/25) ∧ Real.exp (-1/25) ≤ (24019735979/25000000000) := by
  have h := exp_enclosure16 (-1/25) (49875156119873/50000000000000) (99750312239747/100000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((19215788783/20000000000):ℝ) ≤ (49875156119873/50000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((99750312239747/100000000000000):ℝ)^16 ≤ (24019735979/25000000000))⟩

theorem dual_exp_1 : (789569257/20000000000) ≤ Real.exp (-404/125) ∧ Real.exp (-404/125) ≤ (1973923143/50000000000) := by
  have h := exp_enclosure16 (-404/125) (81709492794223/100000000000000) (5106843299639/6250000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((789569257/20000000000):ℝ) ≤ (81709492794223/100000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((5106843299639/6250000000000):ℝ)^16 ≤ (1973923143/50000000000))⟩

theorem dual_exp_2 : (803458443/100000000000) ≤ Real.exp (-603/125) ∧ Real.exp (-603/125) ≤ (200864611/25000000000) := by
  have h := exp_enclosure16 (-603/125) (73970782635463/100000000000000) (9246347829433/12500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((803458443/100000000000):ℝ) ≤ (73970782635463/100000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((9246347829433/12500000000000):ℝ)^16 ≤ (200864611/25000000000))⟩

theorem dual_exp_3 : (80991189/10000000000) ≤ Real.exp (-602/125) ∧ Real.exp (-602/125) ≤ (809911891/100000000000) := by
  have h := exp_enclosure16 (-602/125) (7400777727467/10000000000000) (74007777274671/100000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((80991189/10000000000):ℝ) ≤ (7400777727467/10000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((74007777274671/100000000000000):ℝ)^16 ≤ (809911891/100000000000))⟩

theorem dual_exp_4 : (2021870363/50000000000) ≤ Real.exp (-401/125) ∧ Real.exp (-401/125) ≤ (4043740727/100000000000) := by
  have h := exp_enclosure16 (-401/125) (81832149002573/100000000000000) (40916074501287/50000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((2021870363/50000000000):ℝ) ≤ (81832149002573/100000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((40916074501287/50000000000000):ℝ)^16 ≤ (4043740727/100000000000))⟩

def dualBlankSum : ℝ := (116683381/111921381)*Real.exp (-1/25) +
    (5776405/374319)*Real.exp (-404/125) +
    (1207010/59501)*Real.exp (-603/125) +
    (-405010/19701)*Real.exp (-602/125) +
    (-1505/99)*Real.exp (-401/125)
theorem dual_blank_exact : blank5 4 = 1-dualBlankSum := by
  unfold blank5
  rw [capacity5_survival]
  norm_num [dualBlankSum,eigen5,modes5,Fin.sum_univ_succ]
  ring
theorem dual_blank_lower : 73/10000 < blank5 4 := by
  rw [dual_blank_exact]
  have h0 := dual_exp_0
  have h1 := dual_exp_1
  have h2 := dual_exp_2
  have h3 := dual_exp_3
  have h4 := dual_exp_4
  unfold dualBlankSum
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
theorem dual_miss_lower : 69/1000 < miss5 5 := by
  rw [miss5_exact]
  have h0 := exp_capacity5_0
  have h1 := exp_capacity5_1
  have h2 := exp_capacity5_2
  have h3 := exp_capacity5_3
  have h4 := exp_capacity5_4
  have hm : 377/100 < targetSum5 := by
    unfold targetSum5
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have he := exp_loading.1
  nlinarith [mul_pos (Real.exp_pos (-4)) (sub_pos.mpr hm)]
theorem dual_source_margin : 111/2000 < miss5 5-5*((1/100)-blank5 4) := by
  linarith [dual_blank_lower,dual_miss_lower]
end AssayInformation
