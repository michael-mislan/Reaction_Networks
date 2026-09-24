import proofs.RandomViability.TrajectoryUniqueness

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000

theorem map_compProd_first {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) [hμ : SFinite μ]
    (κ : Kernel A C) [hκ : IsSFiniteKernel κ] (η : Kernel B C) [hη : IsSFiniteKernel η]
    (f : A → B) (hf : Measurable f) (he : ∀ a, κ a = η (f a)) :
    (μ ⊗ₘ κ).map (Prod.map f id) = μ.map f ⊗ₘ η := by
  have hm : Measurable (Prod.map f (id : C → C)) := hf.prodMap measurable_id
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs), Measure.compProd_apply hs,
    lintegral_map' (Kernel.measurable_kernel_prodMk_left hs).aemeasurable hf.aemeasurable]
  apply lintegral_congr
  intro a
  rw [he a]
  rfl

variable {α β : Type*}

def restartJump (z : ℕ → JumpState α β) : ℕ → JumpState α β
  | 0 => ((z 1).1, (Sum.inl (), 0))
  | k+1 => z (k+2)

def restartPrefix (k : ℕ) (h : Finset.Iic (k+1) → JumpState α β) :
    Finset.Iic k → JumpState α β := fun i =>
  if (i : ℕ) = 0 then ((h ⟨1, Finset.mem_Iic.mpr (by omega)⟩).1, (Sum.inl (), 0))
  else h ⟨(i : ℕ)+1, Finset.mem_Iic.mpr (Nat.add_le_add_right (Finset.mem_Iic.mp i.property) 1)⟩

theorem restartPrefix_restrict (k : ℕ) (z : ℕ → JumpState α β) :
    restartPrefix k (Preorder.frestrictLe (k+1) z) = Preorder.frestrictLe k (restartJump z) := by
  funext i
  by_cases hi : (i : ℕ) = 0
  · simp only [restartPrefix, if_pos hi]
    change ((z 1).1, (Sum.inl (), (0 : ℝ))) = restartJump z (i : ℕ)
    rw [hi]
    rfl
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi
    simp only [restartPrefix, if_neg hi]
    change z ((i : ℕ)+1) = restartJump z (i : ℕ)
    rw [hj]
    rfl

theorem restartPrefix_last_population (k : ℕ) (h : Finset.Iic (k+1) → JumpState α β) :
    (restartPrefix k h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1 =
      (h ⟨k+1, Finset.mem_Iic.mpr le_rfl⟩).1 := by
  cases k with
  | zero => rfl
  | succ k => simp only [restartPrefix, Nat.succ_ne_zero, if_false]

variable [MeasurableSpace α] [MeasurableSpace β]

theorem restartJump_measurable : Measurable (@restartJump α β) := by
  apply measurable_pi_lambda
  intro k
  cases k with
  | zero => exact (measurable_pi_apply 1).fst.prodMk measurable_const
  | succ k => exact measurable_pi_apply (k+2)

theorem restartPrefix_measurable (k : ℕ) : Measurable (@restartPrefix α β k) := by
  apply measurable_pi_lambda
  intro i
  unfold restartPrefix
  split_ifs
  · exact (measurable_pi_apply _).fst.prodMk measurable_const
  · exact measurable_pi_apply _

theorem restart_prefix_map (μ : Measure (ℕ → JumpState α β)) (k : ℕ) :
    (μ.map restartJump).map (Preorder.frestrictLe k) =
      (μ.map (Preorder.frestrictLe (k+1))).map (restartPrefix k) := by
  rw [Measure.map_map (Preorder.measurable_frestrictLe k) restartJump_measurable,
    Measure.map_map (restartPrefix_measurable k) (Preorder.measurable_frestrictLe (k+1))]
  congr 1
  funext z
  exact (restartPrefix_restrict k z).symm

variable [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass β] in
theorem restart_history_kernel (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (k : ℕ) (h : Finset.Iic (k+1) → JumpState α β) :
    jumpHistoryKernel next rate hr ht k (restartPrefix k h) =
      jumpHistoryKernel next rate hr ht (k+1) h := by
  change jumpStateKernel next rate hr ht
    (restartPrefix k h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1 =
      jumpStateKernel next rate hr ht (h ⟨k+1, Finset.mem_Iic.mpr le_rfl⟩).1
  rw [restartPrefix_last_population]

end
end RandomViability
