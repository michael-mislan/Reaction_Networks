import proofs.MicrobialFunctionAssay.Sharpness

namespace MicrobialFunctionAssay

/-! ## Exact reserve and activity tolerances for the worked comparison -/

/-- Certificate of the washed worked record as an exact function of the
pre-wash reserve ceiling. -/
theorem reserve_tolerance (J : ℝ) :
    lower (29/5) (19/5) 10 (1/20) (9/10) J (1/5) = max 0 (339/100 - 17/20*J) := by
  have h0 : (0:ℝ) ≤ max 0 (339/100 - 17/20*J) := le_max_left _ _
  have h1 : 339/100 - 17/20*J ≤ max 0 (339/100 - 17/20*J) := le_max_right _ _
  refine le_antisymm ?_ (max_le (lower_nonneg _ _ _ _ _ _ _) ?_)
  · unfold lower
    repeat' apply max_le
    all_goals linarith
  · refine le_trans ?_ (lower_ge_reserve (29/5) (19/5) 10 (1/20) (9/10) J (1/5))
    linarith

/-- Joint activity/reserve-slack budget: the washed certificate in the declared
synthetic response family, with reserve ceiling `2 + δ`. -/
theorem wash_curve_slack (a δ : ℝ) (ha : a ≤ 1) :
    lower (29/5) (17/10 + 21/10*a) 10 (1/20) (9/10) (2 + δ) (1/5)
      = max 0 (21/10*a - 41/100 - 17/20*δ) := by
  have h0 : (0:ℝ) ≤ max 0 (21/10*a - 41/100 - 17/20*δ) := le_max_left _ _
  have h1 : 21/10*a - 41/100 - 17/20*δ
      ≤ max 0 (21/10*a - 41/100 - 17/20*δ) := le_max_right _ _
  refine le_antisymm ?_ (max_le (lower_nonneg _ _ _ _ _ _ _) ?_)
  · unfold lower
    repeat' apply max_le
    all_goals linarith
  · refine le_trans ?_
      (lower_ge_reserve (29/5) (17/10 + 21/10*a) 10 (1/20) (9/10) (2 + δ) (1/5))
    linarith

theorem improvement_criterion_slack (a δ : ℝ) (ha : a ≤ 1) :
    (38/25 < lower (29/5) (17/10 + 21/10*a) 10 (1/20) (9/10) (2 + δ) (1/5))
      ↔ 193/210 + 17/42*δ < a := by
  rw [wash_curve_slack a δ ha, lt_max_iff]
  constructor
  · rintro (h | h)
    · norm_num at h
    · linarith
  · intro h
    right
    linarith

theorem target_criterion_slack (a δ : ℝ) (ha : a ≤ 1) :
    (8/5 ≤ lower (29/5) (17/10 + 21/10*a) 10 (1/20) (9/10) (2 + δ) (1/5))
      ↔ 67/70 + 17/42*δ ≤ a := by
  rw [wash_curve_slack a δ ha, le_max_iff]
  constructor
  · rintro (h | h)
    · norm_num at h
    · linarith
  · intro h
    right
    linarith

/-! ## Two exact material counterexamples -/

noncomputable section

/-- Storage counterexample: mobile product taken up during the first window
raises the pre-wash reserve above its initial ceiling. -/
def storageFirst : Window where
  p0 := 8; r0 := 2; fresh := 0; release := 0; uptake := 2
  collect := 6; lossP := 0; lossR := 0
  nonneg := by norm_num
  enoughR := by norm_num
  enoughP := by norm_num
  release_available := by norm_num

def storageSecond : Window where
  p0 := 0; r0 := 18/5; fresh := 0; release := 18/5; uptake := 0
  collect := 18/5; lossP := 0; lossR := 0
  nonneg := by norm_num
  enoughR := by norm_num
  enoughP := by norm_num
  release_available := by norm_num

def storageWitness : History where
  first := storageFirst
  second := storageSecond
  e := 1/20; s := 9/10; inputP := 0; inputR := 0
  fractions := by norm_num
  inputs_nonneg := by norm_num
  p_recovery := by norm_num [storageFirst, storageSecond, Window.p]
  r_recovery := by norm_num [storageFirst, storageSecond, Window.r]

theorem storage_counterexample :
    storageWitness.first.p0 + storageWitness.first.r0 ≤ 10 ∧
    storageWitness.first.r0 ≤ 2 ∧
    storageWitness.first.uptake ≤ 2 ∧
    storageWitness.first.collect = 6 ∧
    storageWitness.second.collect = 18/5 ∧
    storageWitness.inputP + storageWitness.inputR ≤ 0 ∧
    storageWitness.first.r = 4 ∧
    storageWitness.first.fresh + storageWitness.second.fresh = 0 := by
  norm_num [storageWitness, storageFirst, storageSecond, Window.r]

/-- Substituting the initial reserve ceiling for the pre-wash ceiling issues a
certificate of `17/10` on a history whose true fresh total is `0`. -/
theorem initial_reserve_substitution_unsound :
    lower 6 (18/5) 10 (1/20) (9/10) 2 0 = 17/10 ∧
    storageWitness.first.fresh + storageWitness.second.fresh = 0 := by
  constructor
  · norm_num [lower]
  · norm_num [storageWitness, storageFirst, storageSecond]

/-- The uptake-cap route is sound on the same history: with an initial reserve
bound `2` and a cumulative uptake bound `2` it certifies nothing. -/
theorem uptake_route_sound_here :
    lower 6 (18/5) 10 (1/20) (9/10) (2 + 2) 0 = 0 := by
  norm_num [lower]

/-- Zero-fresh history matching the worked noisy record when the reserve
premise is dropped: both collections lie within the stated error envelopes. -/
def ambiguityFirst : Window where
  p0 := 8; r0 := 2; fresh := 0; release := 0; uptake := 2
  collect := 29/5; lossP := 0; lossR := 0
  nonneg := by norm_num
  enoughR := by norm_num
  enoughP := by norm_num
  release_available := by norm_num

def ambiguitySecond : Window where
  p0 := 1/100; r0 := 19/5; fresh := 0; release := 19/5; uptake := 0
  collect := 381/100; lossP := 0; lossR := 0
  nonneg := by norm_num
  enoughR := by norm_num
  enoughP := by norm_num
  release_available := by norm_num

def ambiguityWitness : History where
  first := ambiguityFirst
  second := ambiguitySecond
  e := 1/20; s := 9/10; inputP := 0; inputR := 1/5
  fractions := by norm_num
  inputs_nonneg := by norm_num
  p_recovery := by norm_num [ambiguityFirst, ambiguitySecond, Window.p]
  r_recovery := by norm_num [ambiguityFirst, ambiguitySecond, Window.r]

theorem reserve_premise_not_redundant :
    |ambiguityWitness.first.collect - 6| ≤ (1/5:ℝ) ∧
    |ambiguityWitness.second.collect - 4| ≤ (1/5:ℝ) ∧
    ambiguityWitness.first.p0 + ambiguityWitness.first.r0 ≤ 10 ∧
    ambiguityWitness.inputP + ambiguityWitness.inputR ≤ 1/5 ∧
    ambiguityWitness.first.r = 4 ∧
    ambiguityWitness.first.fresh + ambiguityWitness.second.fresh = 0 := by
  norm_num [ambiguityWitness, ambiguityFirst, ambiguitySecond, Window.r,
    abs_le]

end
end MicrobialFunctionAssay
