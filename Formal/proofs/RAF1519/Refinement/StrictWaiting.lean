import proofs.RAF1519.Refinement.CountLaw
import proofs.RAF1519.Refinement.HoldingClock

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability Filter

theorem exponential_wait_positive (r : ℝ) : ∀ᵐ x ∂expMeasure r, 0 < x := by
  letI : NoAtoms (expMeasure r) := by
    change NoAtoms (volume.withDensity (exponentialPDF r))
    infer_instance
  have hz : ∀ᵐ x ∂expMeasure r, x ≠ 0 := by
    apply ae_iff.mpr
    simp
  filter_upwards [exponential_wait_nonneg r,hz] with x hx hne
  exact lt_of_le_of_ne hx (Ne.symm hne)

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem jumpState_wait_positive (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) (x : α) :
    ∀ᵐ y ∂jumpStateKernel next rate hr ht x, 0 < y.2.2 := by
  change ∀ᵐ y ∂(jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x), 0 < y.2.2
  rw [ae_map_iff (jumpStateUpdate_measurable next x).aemeasurable
    (measurableSet_lt measurable_const measurable_snd.snd)]
  letI := isProbabilityMeasure_expMeasure (ht x)
  change ∀ᵐ y ∂(jumpLabelPMF (rate x) (hr x) (ht x)).toMeasure.prod (expMeasure (∑ b, rate x b)), 0 < y.2
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)).mpr
  exact Eventually.of_forall (fun _ => exponential_wait_positive _)

theorem jumpTrajectory_wait_positive (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) :
    ∀ᵐ z ∂jumpTrajectoryLaw initial next rate hr ht, ∀ k, 0 < (z (k+1)).2.2 := by
  apply ae_all_iff.mpr
  intro k
  have ha : ∀ᵐ p ∂((jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) ⊗ₘ
      jumpHistoryKernel next rate hr ht k), 0 < p.2.2.2 := by
    apply Measure.ae_compProd_of_ae_ae (measurableSet_lt measurable_const measurable_snd.snd.snd)
    exact Eventually.of_forall (fun h => jumpState_wait_positive next rate hr ht
      (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1)
  have he := @Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (fun _ => JumpState α β) _ (jumpHistoryKernel next rate hr ht) _
    (Measure.dirac (initial, (Sum.inl (), (0 : ℝ)))) _ k
  change (jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) ⊗ₘ
    jumpHistoryKernel next rate hr ht k = (jumpTrajectoryLaw initial next rate hr ht).map
    (fun z => (Preorder.frestrictLe k z, z (k+1))) at he
  rw [he] at ha
  exact ae_of_ae_map (f := fun z : ℕ → JumpState α β =>
    (Preorder.frestrictLe k z, z (k+1))) (by fun_prop) ha

theorem holdingClock_strictMono (h : ℕ → ℝ) (hh : ∀ i, 0 < h i) : StrictMono (holdingClock h) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [holdingClock_succ]
  exact lt_add_of_pos_right _ (hh i)

theorem molecular_wait_positive {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (N : MolecularState n) :
    ∀ᵐ z ∂molecularLaw hn r d k V hr hd hk hV N, ∀ i, 0 < (z (i+1)).2.2 :=
  jumpTrajectory_wait_positive N (molecularNext r d k) (molecularRate r d k V)
    (molecular_rate_nonnegative r d k V hr hd hk hV.le)
    (molecular_total_positive hn r d k V hr hd hk hV)

end
end RAF1519.Refinement
