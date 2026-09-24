import proofs.RandomViability.BindingTrackedModel
import proofs.RandomViability.BindingEntryDeadline

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators

def operatingTrackedKernel (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) : FiniteKernel TrackedCounts :=
  (trackedModel (1/500000000) k r (by norm_num) hk (by linarith)).uniformize
    300000000000 (by norm_num) (tracked_total_bound (1/500000000) k r
      (by norm_num) (by norm_num) hk hk1 (by linarith) hr1)

def entryLift (f : BoxCounts 100000000 → ℝ) (X : TrackedCounts) : ℝ :=
  if trackedPhase X=0 then f (trackedCounts X) else 0

theorem trackedNext_nezero (X : TrackedCounts) (j : Fin 18) (h : trackedPhase X≠0) :
    trackedPhase (trackedNext X j) ≠ 0 := by
  by_cases h2 : trackedPhase X=2
  · simpa only [trackedNext,if_pos h2] using h
  · rw [trackedNext_phase X j h2]
    unfold phaseStep
    rw [if_neg h]
    split_ifs <;> decide

theorem entryLift_next_before (f : BoxCounts 100000000 → ℝ)
    (hf : ∀ N, ¬entryActive 100000000 40000 N → f N=0)
    (X : TrackedCounts) (j : Fin 18) (hp : trackedPhase X=0) :
    entryLift f (trackedNext X j) = f (boxNext 100000000 (trackedCounts X) j) := by
  have hp2 : trackedPhase X≠2 := by omega
  simp only [entryLift,trackedNext_phase X j hp2,trackedNext_counts X j hp2,phaseStep,hp,if_true]
  by_cases hY : 40000≤weightedCount (boxCounts (boxNext 100000000 (trackedCounts X) j))
  · have hn : ¬entryActive 100000000 40000 (boxNext 100000000 (trackedCounts X) j) := by
      intro h
      exact (not_lt_of_ge hY) h.2
    simp [hY,hf _ hn]
  · simp [hY]

theorem operatingEntry_step_outside (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (f : BoxCounts 100000000 → ℝ)
    (N : BoxCounts 100000000) (h : ¬entryActive 100000000 40000 N) :
    (operatingEntryKernel k r hk hk1 hr hr1).step f N = f N := by
  simp [operatingEntryKernel,FiniteJumpModel.uniformize_step,FiniteJumpModel.generator,entryModel,h]

theorem operatingEntry_steps_zero (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (f : BoxCounts 100000000 → ℝ)
    (hf : ∀ N, ¬entryActive 100000000 40000 N → f N=0) (n : ℕ)
    (N : BoxCounts 100000000) (h : ¬entryActive 100000000 40000 N) :
    (operatingEntryKernel k r hk hk1 hr hr1).steps n f N = 0 := by
  induction n with
  | zero => exact hf N h
  | succ n ih =>
    rw [FiniteKernel.steps,operatingEntry_step_outside k r hk hk1 hr hr1 _ N h]
    exact ih

theorem entryLift_step (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (f : BoxCounts 100000000 → ℝ)
    (hf : ∀ N, ¬entryActive 100000000 40000 N → f N=0) (X : TrackedCounts) :
    (operatingTrackedKernel k r hk hk1 hr hr1).step (entryLift f) X =
      entryLift ((operatingEntryKernel k r hk hk1 hr hr1).step f) X := by
  by_cases hp : trackedPhase X=0
  · by_cases hg : resourceGood (boxCounts (trackedCounts X)) 100000000
    · have hen : trackingEnabled X := ⟨by omega,hg⟩
      have hea : entryActive 100000000 40000 (trackedCounts X) := ⟨hg,X.property.1 hp⟩
      have hgen : (trackedModel (1/500000000) k r (by norm_num) hk (by linarith)).generator (entryLift f) X =
          (entryModel 100000000 40000 (1/500000000) k r (by norm_num) (by norm_num) hk (by linarith)).generator f (trackedCounts X) := by
        simp only [FiniteJumpModel.generator,trackedModel,entryModel,if_pos hen,if_pos hea]
        apply Finset.sum_congr rfl
        intro j _
        rw [entryLift_next_before f hf X j hp]
        simp only [entryLift,if_pos hp]
        norm_num only [Nat.cast_ofNat]
      simp only [operatingTrackedKernel,FiniteJumpModel.uniformize_step]
      rw [hgen]
      simp only [entryLift,if_pos hp,operatingEntryKernel,FiniteJumpModel.uniformize_step]
    · have hen : ¬trackingEnabled X := fun h => hg h.2
      have hea : ¬entryActive 100000000 40000 (trackedCounts X) := fun h => hg h.1
      simp only [operatingTrackedKernel,FiniteJumpModel.uniformize_step]
      rw [tracked_generator_outside _ _ _ _ _ _ X _ hen]
      simp only [entryLift,if_pos hp,zero_div,add_zero]
      rw [operatingEntry_step_outside k r hk hk1 hr hr1 f _ hea]
  · have hgen : (trackedModel (1/500000000) k r (by norm_num) hk (by linarith)).generator (entryLift f) X = 0 := by
      simp [FiniteJumpModel.generator,trackedModel,entryLift,hp,trackedNext_nezero X _ hp]
    simp only [operatingTrackedKernel,FiniteJumpModel.uniformize_step]
    rw [hgen]
    simp [entryLift,hp]

theorem entryLift_steps (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (f : BoxCounts 100000000 → ℝ)
    (hf : ∀ N, ¬entryActive 100000000 40000 N → f N=0) (n : ℕ) (X : TrackedCounts) :
    (operatingTrackedKernel k r hk hk1 hr hr1).steps n (entryLift f) X =
      entryLift ((operatingEntryKernel k r hk hk1 hr hr1).steps n f) X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [FiniteKernel.steps,show (operatingTrackedKernel k r hk hk1 hr hr1).steps n (entryLift f) =
      entryLift ((operatingEntryKernel k r hk hk1 hr hr1).steps n f) from funext ih]
    exact entryLift_step k r hk hk1 hr hr1 _ (operatingEntry_steps_zero k r hk hk1 hr hr1 f hf n) X

theorem no_entry_indicator :
    FiniteKernel.eventIndicator {X | trackedPhase X=0 ∧ resourceGood (boxCounts (trackedCounts X)) 100000000} =
      entryLift (FiniteKernel.eventIndicator {N | entryActive 100000000 40000 N}) := by
  funext X
  by_cases hp : trackedPhase X=0
  · have hY : weightedCount (boxCounts (trackedCounts X)) < 40000 := X.property.1 hp
    simp [FiniteKernel.eventIndicator,entryLift,hp,entryActive,hY]
  · simp [FiniteKernel.eventIndicator,entryLift,hp]

theorem tracked_entry_deadline (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) :
    (operatingTrackedKernel k r hk hk1 hr hr1).poissonized 150000000000000
      (FiniteKernel.eventIndicator {X | trackedPhase X=0 ∧ resourceGood (boxCounts (trackedCounts X)) 100000000})
      trackedInitial < 1/12+1/600000000 := by
  rw [no_entry_indicator]
  have hf (N : BoxCounts 100000000) (h : ¬entryActive 100000000 40000 N) :
      FiniteKernel.eventIndicator {N | entryActive 100000000 40000 N} N=0 := by
    simp [FiniteKernel.eventIndicator,h]
  have he : (operatingTrackedKernel k r hk hk1 hr hr1).poissonized 150000000000000
      (entryLift (FiniteKernel.eventIndicator {N | entryActive 100000000 40000 N})) trackedInitial =
      (operatingEntryKernel k r hk hk1 hr hr1).poissonized 150000000000000
        (FiniteKernel.eventIndicator {N | entryActive 100000000 40000 N}) (foodInitial 100000000) := by
    unfold FiniteKernel.poissonized
    apply tsum_congr
    intro n
    rw [entryLift_steps k r hk hk1 hr hr1 _ hf]
    simp [entryLift,trackedInitial,trackedPhase,trackedCounts]
  rw [he]
  exact operating_entry_deadline k r hk hk1 hr hr1 _

end
end RandomViability.Binding
