import proofs.RandomViability.BindingDisabledModel
import proofs.RandomViability.BindingTwoPeriod

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

def disabledExpectation (k r : ℝ) (hk : 0≤k) (hk1 : k≤1/8) (hr : 18≤r) (hr1 : r≤22)
    (f : DisabledState → ℝ) : ℝ :=
  twoPeriod (disabledKernel false k r hk hk1 hr hr1) (disabledKernel true k r hk hk1 hr hr1)
    150000000000000 f disabledInitial

theorem disabled_period_foster (enabled : Bool) (k r : ℝ) (hk : 0≤k) (hk1 : k≤1/8)
    (hr : 18≤r) (hr1 : r≤22) (φ : DisabledState → ℝ) (C : ℝ) (hφ : ∀ X,0≤φ X)
    (hgen : ∀ X,(disabledModel enabled (1/500000000) k r (by norm_num) hk (by linarith)).generator φ X≤C)
    (X : DisabledState) : (disabledKernel enabled k r hk hk1 hr hr1).poissonized 150000000000000 φ X≤φ X+500*C := by
  have hs := (disabledModel enabled (1/500000000) k r (by norm_num) hk (by linarith)).uniformize_drift
    300000000000 (by norm_num) (disabled_total_bound enabled (1/500000000) k r
      (by norm_num) (by norm_num) hk hk1 (by linarith) hr1) φ C hgen
  have h := (disabledKernel enabled k r hk hk1 hr hr1).poissonized_drift_bound
    150000000000000 φ (C/300000000000) hφ hs X
  norm_num only [NNReal.coe_ofNat] at h
  convert h using 1
  ring

theorem disabled_foster (k r : ℝ) (hk : 0≤k) (hk1 : k≤1/8) (hr : 18≤r) (hr1 : r≤22)
    (φ : DisabledState → ℝ) (C : ℝ) (hφ : ∀ X,0≤φ X) (hC : 0≤C)
    (hgen : ∀ enabled X,(disabledModel enabled (1/500000000) k r (by norm_num) hk (by linarith)).generator φ X≤C) :
    disabledExpectation k r hk hk1 hr hr1 φ≤φ disabledInitial+1000*C := by
  have h := twoPeriod_foster (disabledKernel false k r hk hk1 hr hr1) (disabledKernel true k r hk hk1 hr hr1)
    150000000000000 φ (500*C) (500*C) hφ (by positivity)
    (disabled_period_foster false k r hk hk1 hr hr1 φ C hφ (hgen false))
    (disabled_period_foster true k r hk hk1 hr hr1 φ C hφ (hgen true)) disabledInitial
  change disabledExpectation k r hk hk1 hr hr1 φ≤_ at h
  linarith

theorem disabled_inventory_expectation (k r : ℝ) (hk : 0≤k) (hk1 : k≤1/8) (hr : 18≤r) (hr1 : r≤22) :
    disabledExpectation k r hk hk1 hr hr1 disabledInventory≤968 := by
  have hg (enabled X) : (disabledModel enabled (1/500000000) k r (by norm_num) hk (by linarith)).generator
      disabledInventory X≤(121/125:ℝ) := by
    have h := disabled_inventory_foster enabled (1/500000000) k r (by norm_num) hk (by linarith) X
    norm_num at h
    exact h
  have h := disabled_foster k r hk hk1 hr hr1 disabledInventory (121/125) disabledInventory_nonneg (by norm_num) hg
  have hi : disabledInventory disabledInitial=0 := by
    norm_num [disabledInventory,disabledInitial,countProduct,productSpecies,Fin.sum_univ_succ,foodInitial,boxCounts]
  rw [hi] at h
  norm_num at h
  exact h

theorem twoPeriod_scale {α : Type*} [Fintype α] (P Q : FiniteKernel α) (t : ℝ≥0)
    (c : ℝ) (f : α → ℝ) (x : α) : twoPeriod P Q t (fun y=>c*f y) x=c*twoPeriod P Q t f x := by
  unfold twoPeriod
  simp only [Q.poissonized_scale,P.poissonized_scale]

theorem disabled_output_bound (k r : ℝ) (hk : 0≤k) (hk1 : k≤1/8) (hr : 18≤r) (hr1 : r≤22) :
    disabledExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator {X | X.2.val=10000000})≤121/1250000 := by
  have hi (X : DisabledState) : (10000000:ℝ)*FiniteKernel.eventIndicator {X | X.2.val=10000000} X≤disabledInventory X := by
    by_cases h : X.2.val=10000000
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_pos h,mul_one]
      unfold disabledInventory
      rw [h]
      have hn := countProduct_nonneg (boxCounts X.1)
      norm_num
      linarith
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_neg h,mul_zero]
      exact disabledInventory_nonneg X
  have h := twoPeriod_mono (disabledKernel false k r hk hk1 hr hr1) (disabledKernel true k r hk hk1 hr hr1)
    150000000000000 (fun X=>(10000000:ℝ)*FiniteKernel.eventIndicator {X | X.2.val=10000000} X) disabledInventory
    (fun X=>mul_nonneg (by norm_num) (FiniteKernel.eventIndicator_bounds _ X).1) disabledInventory_nonneg hi disabledInitial
  rw [twoPeriod_scale] at h
  change 10000000*disabledExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator {X | X.2.val=10000000})≤
    disabledExpectation k r hk hk1 hr hr1 disabledInventory at h
  have hb := disabled_inventory_expectation k r hk hk1 hr hr1
  linarith

theorem disabled_resource_probability (k r : ℝ) (hk : 0≤k) (hk1 : k≤1/8) (hr : 18≤r) (hr1 : r≤22) :
    disabledExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X.1) 100000000})<1/10000 := by
  let φ := fun X : DisabledState=>resourcePotential 100000000 (boxCounts X.1)
  have hφ (X) : 0≤φ X := resourcePotential_nonneg _ _
  have hi (X : DisabledState) : FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X.1) 100000000} X≤φ X := by
    by_cases h : ¬resourceGood (boxCounts X.1) 100000000
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_pos h]
      exact resourcePotential_exit _ _ h
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_neg h]
      exact hφ X
  have hm := twoPeriod_mono (disabledKernel false k r hk hk1 hr hr1) (disabledKernel true k r hk hk1 hr hr1)
    150000000000000 _ φ (fun X=>(FiniteKernel.eventIndicator_bounds _ X).1) hφ hi disabledInitial
  have hf := disabled_foster k r hk hk1 hr hr1 φ (4*resourceSource 100000000) hφ
    (by unfold resourceSource; positivity)
    (fun enabled=>disabled_resource_foster enabled (1/500000000) k r (by norm_num) (by norm_num) hk hk1 (by linarith) hr1)
  have h := hm.trans hf
  have he : φ disabledInitial=4*Real.exp (-100000) := by
    have hh := foodInitial_potential 100000000
    norm_num at hh
    exact hh
  rw [he] at h
  norm_num [resourceSource] at h
  change disabledExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X.1) 100000000})≤_ at h
  have hb := evaluated_resource_budget
  norm_num at hb
  linarith

/-- A conservative upper event also counts every resource exit as possible output success.
No entry deadline or catalyst-residence condition is imposed on the disabled comparison. -/
theorem disabled_success_upper_bound (k r : ℝ) (hk : 0≤k) (hk1 : k≤1/8) (hr : 18≤r) (hr1 : r≤22) :
    disabledExpectation k r hk hk1 hr hr1
      (FiniteKernel.eventIndicator {X | X.2.val=10000000 ∨ ¬resourceGood (boxCounts X.1) 100000000})<1/5000 := by
  let A : Set DisabledState := {X | X.2.val=10000000}
  let B : Set DisabledState := {X | ¬resourceGood (boxCounts X.1) 100000000}
  have hi (X) : FiniteKernel.eventIndicator (A∪B) X≤FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X := by
    by_cases ha : X∈A <;> by_cases hb : X∈B <;> simp [FiniteKernel.eventIndicator,ha,hb]
  have hm := twoPeriod_mono (disabledKernel false k r hk hk1 hr hr1) (disabledKernel true k r hk hk1 hr hr1)
    150000000000000 _ (fun X=>FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X)
    (fun X=>(FiniteKernel.eventIndicator_bounds _ X).1)
    (fun X=>add_nonneg (FiniteKernel.eventIndicator_bounds A X).1 (FiniteKernel.eventIndicator_bounds B X).1) hi disabledInitial
  rw [twoPeriod_add _ _ _ _ _ (fun X=>(FiniteKernel.eventIndicator_bounds A X).1)
    (fun X=>(FiniteKernel.eventIndicator_bounds B X).1)] at hm
  change disabledExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator (A∪B))≤
    disabledExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator A)+
    disabledExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator B) at hm
  have ho := disabled_output_bound k r hk hk1 hr hr1
  have hr' := disabled_resource_probability k r hk hk1 hr hr1
  change disabledExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator A)≤_ at ho
  change disabledExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator B)<_ at hr'
  change disabledExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator (A∪B))<_
  linarith

end
end RandomViability.Binding
