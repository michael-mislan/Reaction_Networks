import proofs.RandomViability.JumpDisintegration

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000
variable {X : Type*} [MeasurableSpace X]

def appendPrefix (k : ℕ) (p : (Finset.Iic k → X) × X) : Finset.Iic (k+1) → X :=
  fun i => if h : (i : ℕ) ≤ k then p.1 ⟨i, Finset.mem_Iic.mpr h⟩ else p.2

theorem appendPrefix_measurable (k : ℕ) : Measurable (@appendPrefix X k) := by
  apply measurable_pi_lambda
  intro i
  unfold appendPrefix
  split_ifs
  · exact (measurable_pi_apply _).comp measurable_fst
  · exact measurable_snd

omit [MeasurableSpace X] in
theorem appendPrefix_restrict (k : ℕ) (z : ℕ → X) :
    appendPrefix k (Preorder.frestrictLe k z, z (k+1)) = Preorder.frestrictLe (k+1) z := by
  funext i
  unfold appendPrefix
  split_ifs with hi
  · rfl
  · change z (k+1) = z (i : ℕ)
    congr 1
    have hh := Finset.mem_Iic.mp i.property
    omega

theorem trajectory_prefix_ext (μ ν : Measure (ℕ → X)) [hν : IsFiniteMeasure ν]
    (h : ∀ k, μ.map (Preorder.frestrictLe k) = ν.map (Preorder.frestrictLe k)) : μ = ν := by
  let P (I : Finset ℕ) := ν.map I.restrict
  have hP : IsProjectiveMeasureFamily (α := fun _ : ℕ => X) P := by
    intro I J hJI
    dsimp [P]
    rw [Measure.map_map (by apply measurable_pi_lambda; intro i; exact measurable_pi_apply _)
      (by apply measurable_pi_lambda; intro i; exact measurable_pi_apply _)]
    rfl
  letI : ∀ I, IsFiniteMeasure (P I) := fun I => by dsimp [P]; infer_instance
  have hpν : IsProjectiveLimit (α := fun _ : ℕ => X) ν P := fun _ => rfl
  have hpμ : IsProjectiveLimit (α := fun _ : ℕ => X) μ P :=
    (isProjectiveLimit_nat_iff (X := fun _ => X) hP μ).mpr h
  exact hpμ.unique hpν

theorem trajectory_prefix_succ (μ : Measure (ℕ → X))
    (κ : (k : ℕ) → Kernel (Finset.Iic k → X) X)
    (h : ∀ k, μ.map (Preorder.frestrictLe k) ⊗ₘ κ k =
      μ.map (fun z => (Preorder.frestrictLe k z, z (k+1)))) (k : ℕ) :
    μ.map (Preorder.frestrictLe (k+1)) =
      (μ.map (Preorder.frestrictLe k) ⊗ₘ κ k).map (appendPrefix k) := by
  rw [h k, Measure.map_map (appendPrefix_measurable k) (by fun_prop)]
  congr 1
  funext z
  exact (appendPrefix_restrict k z).symm

/-- Initial-prefix and transition identities determine the entire finite-measure trajectory law. -/
theorem trajectory_law_unique (μ ν : Measure (ℕ → X)) [hν : IsFiniteMeasure ν]
    (κ : (k : ℕ) → Kernel (Finset.Iic k → X) X)
    (h0 : μ.map (Preorder.frestrictLe 0) = ν.map (Preorder.frestrictLe 0))
    (hμstep : ∀ k, μ.map (Preorder.frestrictLe k) ⊗ₘ κ k =
      μ.map (fun z => (Preorder.frestrictLe k z, z (k+1))))
    (hνstep : ∀ k, ν.map (Preorder.frestrictLe k) ⊗ₘ κ k =
      ν.map (fun z => (Preorder.frestrictLe k z, z (k+1)))) : μ = ν := by
  apply trajectory_prefix_ext μ ν
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [trajectory_prefix_succ μ κ hμstep k, trajectory_prefix_succ ν κ hνstep k, ih]

end
end RandomViability
