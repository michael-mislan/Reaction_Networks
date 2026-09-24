import proofs.FiniteCopyReactor.EndpointBounds

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

def prefixAlive {α β : Type*} (D : Set α) (k : ℕ) (z : ℕ → JumpState α β) : Prop :=
  ∀ i ≤ k,(z i).1 ∈ D

def killedEndpointObservable {α β : Type*} (D : Set α) (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) : ℝ≥0∞ :=
  ∑' k,if (jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) ∧ prefixAlive D k z then f (z k).1 else 0

theorem restart_state {α β : Type*} (z : ℕ → JumpState α β) (k : ℕ) :
    (restartJump z k).1=(z (k+1)).1 := by cases k <;> rfl

theorem prefix_alive_succ {α β : Type*} (D : Set α) (k : ℕ) (z : ℕ → JumpState α β) :
    prefixAlive D (k+1) z ↔ (z 0).1 ∈ D ∧ prefixAlive D k (restartJump z) := by
  constructor
  · intro h
    refine ⟨h 0 (by omega),?_⟩
    intro i hi
    rw [restart_state]
    exact h (i+1) (by omega)
  · rintro ⟨h0,h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => simpa only [restart_state] using h i (by omega)

theorem killed_observable_split {α β : Type*} (D : Set α) (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) :
    killedEndpointObservable D f T z=if (z 0).1 ∈ D then
      (if 0 ≤ T ∧ T < (z 1).2.2 then f (z 0).1 else 0)+
        killedEndpointObservable D f (T-(z 1).2.2) (restartJump z) else 0 := by
  by_cases hD : (z 0).1 ∈ D
  · rw [if_pos hD]
    unfold killedEndpointObservable
    rw [tsum_eq_zero_add' ENNReal.summable]
    have h0 : jumpElapsed z 0=0 := rfl
    have h1 : jumpElapsed z (0+1)=(z 1).2.2 := by simp [jumpElapsed]
    have hp0 : prefixAlive D 0 z := by
      intro i hi
      have hi0 : i=0 := by omega
      simpa only [hi0] using hD
    rw [h0,h1]
    simp only [hp0,and_true]
    congr 1
    apply tsum_congr
    intro k
    have ht : jumpElapsed z (k+1) ≤ T ∧ T < jumpElapsed z (k+1+1) ↔
        jumpElapsed (restartJump z) k ≤ T-(z 1).2.2 ∧
          T-(z 1).2.2 < jumpElapsed (restartJump z) (k+1) := by
      rw [show jumpElapsed z (k+1)=(z 1).2.2+jumpElapsed (restartJump z) k from restart_wait_sum z k,
        show jumpElapsed z (k+1+1)=(z 1).2.2+jumpElapsed (restartJump z) (k+1) from restart_wait_sum z (k+1)]
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    simp only [ht,prefix_alive_succ,hD,true_and,restart_state]
  · rw [if_neg hD]
    have hp (k : ℕ) : ¬prefixAlive D k z := fun h => hD (h 0 (Nat.zero_le k))
    simp only [killedEndpointObservable,hp,and_false,if_false,tsum_zero]

theorem killed_observable_le {α β : Type*} (D : Set α) (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) : killedEndpointObservable D f T z ≤ endpointObservable f T z := by
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases h : jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)
  · simp only [h,true_and,if_true]
    split_ifs <;> simp
  · simp only [h,false_and,if_false,le_refl]

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] [MeasurableSpace β]

theorem killed_observable_measurable (D : Set α) (f : α → ℝ≥0∞) :
    Measurable (fun p : ℝ × (ℕ → JumpState α β) => killedEndpointObservable D f p.1 p.2) := by
  have hD : MeasurableSet D := (Set.to_countable D).measurableSet
  have hp (k : ℕ) : MeasurableSet {p : ℝ × (ℕ → JumpState α β) | prefixAlive D k p.2} := by
    simp only [prefixAlive,Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
      hD.preimage ((measurable_pi_apply i).comp measurable_snd).fst))
  unfold killedEndpointObservable
  apply Measurable.tsum
  intro k
  exact Measurable.ite
    (((measurableSet_le ((jumpElapsed_measurable k).comp measurable_snd) measurable_fst).inter
      (measurableSet_lt measurable_fst ((jumpElapsed_measurable (k+1)).comp measurable_snd))).inter (hp k))
    ((measurable_of_countable f).comp ((measurable_pi_apply k).comp measurable_snd).fst) measurable_const

end
end FiniteCopyReactor
