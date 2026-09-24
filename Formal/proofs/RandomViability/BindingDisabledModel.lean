import proofs.RandomViability.BindingDisabledChannels

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

abbrev DisabledState := BoxCounts 100000000 × Fin 10000001

def disabledNext (enabled : Bool) (X : DisabledState) (j : Fin 18) : DisabledState :=
  (boxNext 100000000 X.1 j,⟨min 10000000 (X.2.val+(if enabled then exportUnits j else 0)),by
    have h := Nat.min_le_left 10000000 (X.2.val+(if enabled then exportUnits j else 0))
    omega⟩)

/-- Only resource exit stops the disabled model. It has no entry condition. -/
def disabledModel (enabled : Bool) (eps k r : ℝ) (heps : 0≤eps) (hk : 0≤k) (hr : 0≤r) :
    FiniteJumpModel DisabledState (Fin 18) where
  next := disabledNext enabled
  rate X j := if resourceGood (boxCounts X.1) 100000000 then disabledRate (boxCounts X.1) 100000000 eps k r j else 0
  nonneg X j := by
    split_ifs
    · exact disabledRate_nonneg _ _ _ _ _ (by norm_num) heps hk hr j
    · rfl

theorem disabled_total_bound (enabled : Bool) (eps k r : ℝ) (heps : 0≤eps) (heps1 : eps≤1)
    (hk : 0≤k) (hk1 : k≤1/8) (hr : 0≤r) (hr1 : r≤22) (X : DisabledState) :
    (disabledModel enabled eps k r heps hk hr).total X≤300000000000 := by
  by_cases h : resourceGood (boxCounts X.1) 100000000
  · simp only [FiniteJumpModel.total,disabledModel,if_pos h]
    have hm := Finset.sum_le_sum (fun j (_ : j∈Finset.univ)=>
      disabledRate_le (boxCounts X.1) 100000000 eps k r (by norm_num) heps hk hr j)
    have hb := total_rate_bound (boxCounts X.1) 100000000 eps k r (by norm_num) heps heps1 hk hk1 hr hr1 (by
      intro i
      have hi := resource_count_cap (boxCounts X.1) 100000000 h i
      norm_num at hi ⊢
      linarith)
    norm_num at hb
    exact hm.trans hb
  · simp [FiniteJumpModel.total,disabledModel,h]

def disabledKernel (enabled : Bool) (k r : ℝ) (hk : 0≤k) (hk1 : k≤1/8)
    (hr : 18≤r) (hr1 : r≤22) : FiniteKernel DisabledState :=
  (disabledModel enabled (1/500000000) k r (by norm_num) hk (by linarith)).uniformize
    300000000000 (by norm_num) (disabled_total_bound enabled (1/500000000) k r
      (by norm_num) (by norm_num) hk hk1 (by linarith) hr1)

def disabledInitial : DisabledState := (foodInitial 100000000,0)
def disabledInventory (X : DisabledState) : ℝ := countProduct (boxCounts X.1)+(X.2.val:ℝ)

theorem disabledInventory_nonneg (X : DisabledState) : 0≤disabledInventory X :=
  add_nonneg (countProduct_nonneg _) (Nat.cast_nonneg _)

theorem disabled_counter_increment (enabled : Bool) (X : DisabledState) (j : Fin 18) :
    ((disabledNext enabled X j).2.val:ℝ)-(X.2.val:ℝ)≤exportMark j := by
  have hn : (disabledNext enabled X j).2.val≤X.2.val+exportUnits j := by
    have h := Nat.min_le_right 10000000 (X.2.val+(if enabled then exportUnits j else 0))
    change min 10000000 (X.2.val+(if enabled then exportUnits j else 0))≤_
    cases enabled <;> simp only [Bool.false_eq_true,if_false,if_true,add_zero] at h ⊢ <;> omega
  have hr : ((disabledNext enabled X j).2.val:ℝ)≤(X.2.val:ℝ)+(exportUnits j:ℝ) := by exact_mod_cast hn
  rw [exportUnits_real] at hr
  linarith

theorem disabled_inventory_foster (enabled : Bool) (eps k r : ℝ) (heps : 0≤eps) (hk : 0≤k) (hr : 0≤r)
    (X : DisabledState) :
    (disabledModel enabled eps k r heps hk hr).generator disabledInventory X≤(121/25)*eps*100000000 := by
  by_cases h : resourceGood (boxCounts X.1) 100000000
  · have hm : (disabledModel enabled eps k r heps hk hr).generator disabledInventory X≤
        ∑ j,disabledRate (boxCounts X.1) 100000000 eps k r j*
          (countProduct (countNext (boxCounts X.1) j)-countProduct (boxCounts X.1)+exportMark j) := by
      simp only [FiniteJumpModel.generator,disabledModel,if_pos h]
      apply Finset.sum_le_sum
      intro j _
      have hc := disabled_counter_increment enabled X j
      have hh := mul_le_mul_of_nonneg_left hc (disabledRate_nonneg (boxCounts X.1) 100000000 eps k r (by norm_num) heps hk hr j)
      unfold disabledInventory
      change disabledRate (boxCounts X.1) 100000000 eps k r j*
        (countProduct (boxCounts (boxNext 100000000 X.1 j))+((disabledNext enabled X j).2.val:ℝ)-
          (countProduct (boxCounts X.1)+(X.2.val:ℝ)))≤_
      rw [boxNext_exact 100000000 X.1 j h]
      nlinarith only [hh]
    apply hm.trans
    apply disabled_basal_bound (boxCounts X.1) 100000000 eps k r (by norm_num) heps hk
    · have hi := resource_count_cap (boxCounts X.1) 100000000 h 0
      norm_num only [Nat.cast_ofNat] at hi
      norm_num
      exact_mod_cast hi
    · have hi := resource_count_cap (boxCounts X.1) 100000000 h 1
      norm_num only [Nat.cast_ofNat] at hi
      norm_num
      exact_mod_cast hi
  · simp only [FiniteJumpModel.generator,disabledModel,if_neg h,zero_mul,Finset.sum_const_zero]
    positivity

theorem disabled_resource_foster (enabled : Bool) (eps k r : ℝ) (heps : 0≤eps) (heps1 : eps≤1)
    (hk : 0≤k) (hk1 : k≤1/8) (hr : 0≤r) (hr1 : r≤22) (X : DisabledState) :
    (disabledModel enabled eps k r heps hk hr).generator (fun Z=>resourcePotential 100000000 (boxCounts Z.1)) X≤
      4*resourceSource 100000000 := by
  by_cases h : resourceGood (boxCounts X.1) 100000000
  · have he : (disabledModel enabled eps k r heps hk hr).generator
        (fun Z=>resourcePotential 100000000 (boxCounts Z.1)) X =
        disabledGenerator (boxCounts X.1) 100000000 eps k r (resourcePotential 100000000) := by
      simp only [FiniteJumpModel.generator,disabledModel,if_pos h,disabledGenerator,disabledNext]
      apply Finset.sum_congr rfl
      intro j _
      rw [boxNext_exact 100000000 X.1 j h]
    rw [he,disabled_resource_generator]
    have hh := stopped_resource_foster 100000000 eps k r (by norm_num) heps heps1 hk hk1 hr hr1 X.1
    rw [stopped_generator_inside 100000000 eps k r (by norm_num) heps hk hr X.1 _ h] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  · simp only [FiniteJumpModel.generator,disabledModel,if_neg h,zero_mul,Finset.sum_const_zero]
    unfold resourceSource
    positivity

end
end RandomViability.Binding
