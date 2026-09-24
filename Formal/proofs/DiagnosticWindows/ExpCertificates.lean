import proofs.DiagnosticWindows.ExponentialBounds

namespace DiagnosticWindows

theorem exp_loading : (9157819/500000000) ≤ Real.exp (-4) ∧
    Real.exp (-4) ≤ (18315639/1000000000) := by
  have h := exp_enclosure16 (-4) (778800783071/1000000000000) (24337524471/31250000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((9157819/500000000):ℝ) ≤ (778800783071/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((24337524471/31250000000):ℝ)^16 ≤ (18315639/1000000000))⟩

theorem exp_capacity10_0 : (484253291/500000000) ≤ Real.exp (-4/125) ∧
    Real.exp (-4/125) ≤ (968506583/1000000000) := by
  have h := exp_enclosure16 (-4/125) (998001998667/1000000000000) (249500499667/250000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((484253291/500000000):ℝ) ≤ (998001998667/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((249500499667/250000000000):ℝ)^16 ≤ (968506583/1000000000))⟩

theorem exp_capacity10_1 : (54541139/1000000000) ≤ Real.exp (-1818/625) ∧
    Real.exp (-1818/625) ≤ (2727057/50000000) := by
  have h := exp_enclosure16 (-1818/625) (208442019339/250000000000) (833768077357/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((54541139/1000000000):ℝ) ≤ (208442019339/250000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((833768077357/1000000000000):ℝ)^16 ≤ (2727057/50000000))⟩

theorem exp_capacity10_2 : (2912489/500000000) ≤ Real.exp (-3216/625) ∧
    Real.exp (-3216/625) ≤ (5824979/1000000000) := by
  have h := exp_enclosure16 (-3216/625) (724988127589/1000000000000) (72498812759/100000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((2912489/500000000):ℝ) ≤ (724988127589/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((72498812759/100000000000):ℝ)^16 ≤ (5824979/1000000000))⟩

theorem exp_capacity10_3 : (294953/250000000) ≤ Real.exp (-4214/625) ∧
    Real.exp (-4214/625) ≤ (1179813/1000000000) := by
  have h := exp_enclosure16 (-4214/625) (41007974867/62500000000) (656127597873/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((294953/250000000):ℝ) ≤ (41007974867/62500000000)^16).trans h.1,
    h.2.trans (by norm_num : ((656127597873/1000000000000):ℝ)^16 ≤ (1179813/1000000000))⟩

theorem exp_capacity10_4 : (453189/1000000000) ≤ Real.exp (-4812/625) ∧
    Real.exp (-4812/625) ≤ (45319/100000000) := by
  have h := exp_enclosure16 (-4812/625) (618041297081/1000000000000) (309020648541/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((453189/1000000000):ℝ) ≤ (618041297081/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((309020648541/500000000000):ℝ)^16 ≤ (45319/100000000))⟩

theorem exp_capacity5_0 : (59451839/62500000) ≤ Real.exp (-1/20) ∧
    Real.exp (-1/20) ≤ (38049177/40000000) := by
  have h := exp_enclosure16 (-1/20) (99687987773/100000000000) (996879877731/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((59451839/62500000):ℝ) ≤ (99687987773/100000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((996879877731/1000000000000):ℝ)^16 ≤ (38049177/40000000))⟩

theorem exp_capacity5_1 : (549921/31250000) ≤ Real.exp (-101/25) ∧
    Real.exp (-101/25) ≤ (17597473/1000000000) := by
  have h := exp_enclosure16 (-101/25) (776856212839/1000000000000) (19421405321/25000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((549921/31250000):ℝ) ≤ (776856212839/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((19421405321/25000000000):ℝ)^16 ≤ (17597473/1000000000))⟩

theorem exp_capacity5_2 : (2405493/1000000000) ≤ Real.exp (-603/100) ∧
    Real.exp (-603/100) ≤ (1202747/500000000) := by
  have h := exp_enclosure16 (-603/100) (171500454691/250000000000) (137200363753/200000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((2405493/1000000000):ℝ) ≤ (171500454691/250000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((137200363753/200000000000):ℝ)^16 ≤ (1202747/500000000))⟩

theorem exp_capacity5_3 : (2429669/1000000000) ≤ Real.exp (-301/50) ∧
    Real.exp (-301/50) ≤ (242967/100000000) := by
  have h := exp_enclosure16 (-301/50) (686430703913/1000000000000) (343215351957/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((2429669/1000000000):ℝ) ≤ (686430703913/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((343215351957/500000000000):ℝ)^16 ≤ (242967/100000000))⟩

theorem exp_capacity5_4 : (3626679/200000000) ≤ Real.exp (-401/100) ∧
    Real.exp (-401/100) ≤ (4533349/250000000) := by
  have h := exp_enclosure16 (-401/100) (778314184659/1000000000000) (38915709233/50000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((3626679/200000000):ℝ) ≤ (778314184659/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((38915709233/50000000000):ℝ)^16 ≤ (4533349/250000000))⟩

end DiagnosticWindows
