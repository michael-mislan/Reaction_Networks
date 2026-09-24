import proofs.RandomViability.BindingExportTilt
import proofs.FiniteCopy.KernelExpectations

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

def outputActive (X : OutputState) : Prop :=
  trackingEnabled X.1 ∧ trackedPhase X.1=1 ∧ X.2.val<10000000

def outputTest (X : OutputState) : ℝ := if outputActive X then Real.exp (-(X.2.val:ℝ)/8) else 0

theorem outputTest_nonneg (X : OutputState) : 0 ≤ outputTest X := by
  unfold outputTest
  split_ifs <;> positivity

theorem outputTest_le_one (X : OutputState) : outputTest X ≤ 1 := by
  unfold outputTest
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    have h := Nat.cast_nonneg (α := ℝ) X.2.val
    linarith
  · norm_num

theorem outputTest_next_bound (X : OutputState) (j : Fin 18) :
    outputTest (outputNext true X j) ≤ Real.exp (-(X.2.val:ℝ)/8)*Real.exp (-(exportUnits j:ℝ)/8) := by
  unfold outputTest
  split_ifs with h
  · have hc := h.2.2
    change min 10000000 (X.2.val+exportUnits j)<10000000 at hc
    have hm : X.2.val+exportUnits j ≤ 10000000 := by omega
    change Real.exp (-((min 10000000 (X.2.val+exportUnits j):ℕ):ℝ)/8) ≤ _
    rw [Nat.min_eq_right hm,Nat.cast_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    apply le_of_eq
    ring
  · positivity

theorem output_inactive_generator (eps k r : ℝ) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (X : OutputState) (h : ¬outputActive X) :
    (outputModel true eps k r heps hk hr).generator outputTest X=0 := by
  by_cases hen : trackingEnabled X.1
  · by_cases hp : trackedPhase X.1=0
    · exact output_generator_deadline_failure eps k r heps hk hr outputTest X hp
    · have hp1 : trackedPhase X.1=1 := by have hh := hen.1; omega
      have hc : X.2.val=10000000 := by
        have hlt := X.2.isLt
        have hh : ¬X.2.val<10000000 := fun hh => h ⟨hen,hp1,hh⟩
        omega
      have hn (j : Fin 18) : outputTest (outputNext true X j)=0 := by
        unfold outputTest
        split_ifs with hnext
        · have hh := hnext.2.2
          change min 10000000 (X.2.val+exportUnits j)<10000000 at hh
          omega
        · rfl
      simp only [FiniteJumpModel.generator,outputModel]
      simp only [hn]
      simp [outputTest,h]
  · simp [FiniteJumpModel.generator,outputModel,trackedModel,hen]

theorem output_generator_decay (eps k r : ℝ) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (X : OutputState) :
    (outputModel true eps k r heps hk hr).generator outputTest X ≤ -(100000/27)*outputTest X := by
  by_cases h : outputActive X
  · have hp0 : trackedPhase X.1≠0 := by have hh := h.2.1; omega
    have hY : 20000 ≤ weightedCount (boxCounts (trackedCounts X.1)) := X.1.property.2.1 h.2.1
    have hg := export_tilt_floor (boxCounts (trackedCounts X.1)) 100000000 eps k r hY
    calc
      _ ≤ Real.exp (-(X.2.val:ℝ)/8)*
          (∑ j,countRate (boxCounts (trackedCounts X.1)) 100000000 eps k r j*
            (Real.exp (-(exportUnits j:ℝ)/8)-1)) := by
        simp only [FiniteJumpModel.generator,outputModel,true_and,if_neg hp0,trackedModel,if_pos h.1,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        have hn := outputTest_next_bound X j
        have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right hn (outputTest X))
          (countRate_nonneg (boxCounts (trackedCounts X.1)) 100000000 eps k r (by norm_num) heps hk hr j)
        have hcurr : outputTest X=Real.exp (-(X.2.val:ℝ)/8) := by simp [outputTest,h]
        rw [hcurr] at hh ⊢
        convert hh using 1
        ring
      _ ≤ Real.exp (-(X.2.val:ℝ)/8)*(-(100000:ℝ)/27) :=
        mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
      _ = _ := by rw [outputTest,if_pos h]; ring
  · rw [output_inactive_generator eps k r heps hk hr X h]
    simp [outputTest,h]

theorem output_indicator_bound (X : OutputState) :
    FiniteKernel.eventIndicator {X | outputActive X} X ≤ Real.exp 1250000*outputTest X := by
  by_cases h : outputActive X
  · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_pos h,outputTest]
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have hc : (X.2.val:ℝ) ≤ 10000000 := by exact_mod_cast h.2.2.le
    linarith
  · simp [FiniteKernel.eventIndicator,outputTest,h]

theorem output_probability (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (X : OutputState) :
    (operatingOutputKernel true k r hk hk1 hr hr1).poissonized 150000000000000
      (FiniteKernel.eventIndicator {X | outputActive X}) X < 1/10000 := by
  let P := operatingOutputKernel true k r hk hk1 hr hr1
  have hdec := (outputModel true (1/500000000) k r (by norm_num) hk (by linarith)).uniformized_decay_bound
    300000000000 500 (by norm_num)
    (output_total_bound true (1/500000000) k r (by norm_num) (by norm_num) hk hk1 (by linarith) hr1)
    outputTest outputTest_nonneg (100000/27) (by norm_num)
    (output_generator_decay (1/500000000) k r (by norm_num) hk (by linarith)) X
  rw [show (300000000000:ℝ≥0)*500=150000000000000 by norm_num] at hdec
  norm_num only [NNReal.coe_ofNat] at hdec
  have hi := P.poissonized_mono 150000000000000
    (FiniteKernel.eventIndicator {X | outputActive X}) (fun Z => Real.exp 1250000*outputTest Z)
    (by intro Z; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (fun Z => mul_nonneg (Real.exp_pos _).le (outputTest_nonneg Z)) output_indicator_bound X
  rw [P.poissonized_scale] at hi
  have ht := mul_le_mul_of_nonneg_left (outputTest_le_one X) (Real.exp_pos (-(50000000/27:ℝ))).le
  have hh := hdec.trans (by simpa only [mul_one] using ht)
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (1250000:ℝ)).le
  have he : Real.exp 1250000*Real.exp (-(50000000/27:ℝ)) = Real.exp (-(16250000:ℝ)/27) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  rw [he] at hm
  exact (hi.trans hm).trans_lt evaluated_export_budget

end
end RandomViability.Binding
