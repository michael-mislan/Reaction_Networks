import proofs.RandomViability.BindingOutputModel
import proofs.RandomViability.BindingTrackedReturn
import proofs.RandomViability.BindingTwoPeriod

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

def resourceFailure (X : OutputState) : Prop :=
  ¬resourceGood (boxCounts (trackedCounts X.1)) 100000000
def returnFailure (X : OutputState) : Prop := trackedPhase X.1=2
def missedEntry (X : OutputState) : Prop :=
  trackedPhase X.1=0 ∧ resourceGood (boxCounts (trackedCounts X.1)) 100000000

def operatingExpectation (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (f : OutputState → ℝ) : ℝ :=
  twoPeriod (operatingOutputKernel false k r hk hk1 hr hr1)
    (operatingOutputKernel true k r hk hk1 hr hr1) 150000000000000 f outputInitial

theorem tracked_resource_foster (eps k r : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr1 : r ≤ 22) (X : TrackedCounts) :
    (trackedModel eps k r heps hk hr).generator
      (fun Z=>resourcePotential 100000000 (boxCounts (trackedCounts Z))) X ≤ 4*resourceSource 100000000 := by
  by_cases h : trackingEnabled X
  · rw [tracked_generator_inside eps k r heps hk hr X _ h]
    have hh := stopped_resource_foster 100000000 eps k r (by norm_num) heps heps1 hk hk1 hr hr1 (trackedCounts X)
    rw [stopped_generator_inside 100000000 eps k r (by norm_num) heps hk hr (trackedCounts X) _ h.2] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  · rw [tracked_generator_outside eps k r heps hk hr X _ h]
    unfold resourceSource
    positivity

theorem output_period_foster (enabled : Bool) (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (φ : TrackedCounts → ℝ) (C : ℝ)
    (hφ : ∀ X,0≤φ X) (hC : 0≤C)
    (hgen : ∀ X,(trackedModel (1/500000000) k r (by norm_num) hk (by linarith)).generator φ X≤C)
    (X : OutputState) :
    (operatingOutputKernel enabled k r hk hk1 hr hr1).poissonized 150000000000000
      (fun Z=>φ Z.1) X ≤ φ X.1+500*C := by
  have hg (Z : OutputState) : (outputModel enabled (1/500000000) k r (by norm_num) hk (by linarith)).generator
      (fun W=>φ W.1) Z ≤ C := by
    by_cases h : enabled=true ∧ trackedPhase Z.1=0
    · rw [h.1,output_generator_deadline_failure _ _ _ _ _ _ _ Z h.2]
      exact hC
    · rw [output_generator_project enabled _ _ _ _ _ _ φ Z h]
      exact hgen Z.1
  have hs := (outputModel enabled (1/500000000) k r (by norm_num) hk (by linarith)).uniformize_drift
    300000000000 (by norm_num)
    (output_total_bound enabled (1/500000000) k r (by norm_num) (by norm_num) hk hk1 (by linarith) hr1)
    (fun Z=>φ Z.1) C hg
  have h := (operatingOutputKernel enabled k r hk hk1 hr hr1).poissonized_drift_bound
    150000000000000 (fun Z=>φ Z.1) (C/300000000000) (fun Z=>hφ Z.1) hs X
  norm_num only [NNReal.coe_ofNat] at h
  convert h using 1
  ring

theorem operating_foster (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (φ : TrackedCounts → ℝ) (C : ℝ)
    (hφ : ∀ X,0≤φ X) (hC : 0≤C)
    (hgen : ∀ X,(trackedModel (1/500000000) k r (by norm_num) hk (by linarith)).generator φ X≤C) :
    operatingExpectation k r hk hk1 hr hr1 (fun X=>φ X.1) ≤ φ trackedInitial+1000*C := by
  have h := twoPeriod_foster (operatingOutputKernel false k r hk hk1 hr hr1)
    (operatingOutputKernel true k r hk hk1 hr hr1) 150000000000000 (fun X=>φ X.1)
    (500*C) (500*C) (fun X=>hφ X.1) (by positivity)
    (output_period_foster false k r hk hk1 hr hr1 φ C hφ hC hgen)
    (output_period_foster true k r hk hk1 hr hr1 φ C hφ hC hgen) outputInitial
  change operatingExpectation k r hk hk1 hr hr1 (fun X=>φ X.1) ≤ _ at h
  change operatingExpectation k r hk hk1 hr hr1 (fun X=>φ X.1) ≤ φ trackedInitial+1000*C
  change _ ≤ φ trackedInitial+500*C+500*C at h
  linarith

theorem operating_resource_failure (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) :
    operatingExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator {X | resourceFailure X}) < 1/10000 := by
  let φ := fun X : TrackedCounts=>resourcePotential 100000000 (boxCounts (trackedCounts X))
  have hφ (X) : 0≤φ X := resourcePotential_nonneg _ _
  have hi (X : OutputState) : FiniteKernel.eventIndicator {X | resourceFailure X} X≤φ X.1 := by
    by_cases h : resourceFailure X
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_pos h]
      exact resourcePotential_exit _ _ h
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_neg h]
      exact hφ X.1
  have hm := twoPeriod_mono (operatingOutputKernel false k r hk hk1 hr hr1)
    (operatingOutputKernel true k r hk hk1 hr hr1) 150000000000000 _ (fun X=>φ X.1)
    (fun X=>(FiniteKernel.eventIndicator_bounds _ X).1) (fun X=>hφ X.1) hi outputInitial
  have hf := operating_foster k r hk hk1 hr hr1 φ (4*resourceSource 100000000) hφ
    (by unfold resourceSource; positivity)
    (tracked_resource_foster (1/500000000) k r (by norm_num) (by norm_num) hk hk1 (by linarith) hr1)
  have h := hm.trans hf
  have he : φ trackedInitial = 4*Real.exp (-100000) := by
    change resourcePotential 100000000 (boxCounts (foodInitial 100000000)) = _
    have h₀ := foodInitial_potential 100000000
    norm_num at h₀
    exact h₀
  rw [he] at h
  norm_num [resourceSource] at h
  change operatingExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator {X | resourceFailure X}) ≤ _ at h
  have hb := evaluated_resource_budget
  norm_num at hb
  linarith

theorem operating_return_failure (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) :
    operatingExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator {X | returnFailure X}) < 1/10000 := by
  have hi (X : OutputState) : FiniteKernel.eventIndicator {X | returnFailure X} X≤trackedReturnPotential X.1 := by
    by_cases h : returnFailure X
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_pos h]
      exact tracked_return_exit X.1 h
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_neg h]
      exact tracked_return_nonneg X.1
  have hm := twoPeriod_mono (operatingOutputKernel false k r hk hk1 hr hr1)
    (operatingOutputKernel true k r hk hk1 hr hr1) 150000000000000 _ (fun X=>trackedReturnPotential X.1)
    (fun X=>(FiniteKernel.eventIndicator_bounds _ X).1) (fun X=>tracked_return_nonneg X.1) hi outputInitial
  have hf := operating_foster k r hk hk1 hr hr1 trackedReturnPotential returnSource tracked_return_nonneg
    (by unfold returnSource; positivity)
    (tracked_return_foster (1/500000000) k r (by norm_num) (by norm_num) hk hk1 hr hr1)
  have h := hm.trans hf
  rw [tracked_initial_return] at h
  exact h.trans_lt evaluated_return_budget

end
end RandomViability.Binding
