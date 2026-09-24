import proofs.CompositionalMemory.CountCutoff
import proofs.RandomViability.JumpSupport
import proofs.RandomViability.JumpInitial
import proofs.RandomViability.JumpWaitingSupport

namespace CompositionalMemory
open FiniteCopy RandomViability MeasureTheory ProbabilityTheory

instance modularChannel_singletons (k : ℕ) : MeasurableSingletonClass (ModularChannel k) := by
  constructor
  intro r
  cases r with
  | inl p => simpa only [Set.image_singleton] using (measurableSet_singleton p).inl_image
  | inr r =>
    cases r with
    | inl p =>
      have h : MeasurableSet ({Sum.inl p} : Set ((Fin k × Fin k) ⊕ Fin k)) := by
        simpa only [Set.image_singleton] using (measurableSet_singleton p).inl_image
      simpa only [Set.image_singleton] using h.inr_image
    | inr i =>
      have h : MeasurableSet ({Sum.inr i} : Set ((Fin k × Fin k) ⊕ Fin k)) := by
        simpa only [Set.image_singleton] using (measurableSet_singleton i).inr_image
      simpa only [Set.image_singleton] using h.inr_image

abbrev PositiveCountState (k : ℕ) := {s : ModularCountState k // 0 < s.2}

def positiveCountNext {k : ℕ} (s : PositiveCountState k) (r : ModularChannel k) : PositiveCountState k :=
  ⟨modularNext s.val r,modular_membrane_positive s.val s.property r⟩

theorem modular_total_positive {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (s : PositiveCountState k) : 0 < ∑ r, modularRate γ w s.val r := by
  let i : Fin k := ⟨0,by omega⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hmR : (0 : ℝ) < s.val.2 := by exact_mod_cast s.property
  have hp : 0 < modularRate γ w s.val (.inl (i,6)) := by
    change 0 < ((s.val.2 : ℝ)/k)*6
    positivity
  exact hp.trans_le (Finset.single_le_sum
    (fun r _ => modular_rate_nonnegative γ w hγ hw s.val r) (Finset.mem_univ _))

/-- Actual marked jump law in rescaled time, with state-dependent exponential
holding times and literal reaction labels. Nonexplosion is a separate theorem. -/
noncomputable def countJumpTrajectory {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (s : PositiveCountState k) : Measure (ℕ → JumpState (PositiveCountState k) (ModularChannel k)) :=
  jumpTrajectoryLaw s positiveCountNext (fun x r => modularRate γ w x.val r)
    (fun x r => modular_rate_nonnegative γ w hγ hw x.val r)
    (modular_total_positive hk γ w hγ hw)

instance countJumpTrajectory_probability {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (s : PositiveCountState k) : IsProbabilityMeasure (countJumpTrajectory hk γ w hγ hw s) := by
  unfold countJumpTrajectory
  infer_instance

theorem count_jump_wait_nonnegative {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (s : PositiveCountState k) :
    ∀ᵐ z ∂countJumpTrajectory hk γ w hγ hw s, ∀ j, 0 ≤ (z (j+1)).2.2 :=
  jumpTrajectory_wait_nonneg s positiveCountNext (fun x r => modularRate γ w x.val r)
    (fun x r => modular_rate_nonnegative γ w hγ hw x.val r)
    (modular_total_positive hk γ w hγ hw)

end CompositionalMemory
