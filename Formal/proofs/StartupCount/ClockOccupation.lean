import proofs.RandomViability.JumpLaplace
import proofs.RandomViability.CensoredExponentialClock
import proofs.RandomViability.JumpStateLaplace
import proofs.RandomViability.ChronologicalReward

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 40000

def activeClockWeight (R u : ℝ) : ℝ≥0∞ :=
  if 0 ≤ u then expMeasure R (Ioi u) else 0

theorem activeClockWeight_measurable (R : ℝ) (hR : 0 < R) :
    Measurable (activeClockWeight R) := by
  have he : activeClockWeight R = fun u => if 0 ≤ u then ENNReal.ofReal (Real.exp (-R*u)) else 0 := by
    funext u
    by_cases hu : 0 ≤ u
    · simp only [activeClockWeight,if_pos hu,exponential_Ioi R u hR hu]
    · simp only [activeClockWeight,if_neg hu]
  rw [he]
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) (by fun_prop) measurable_const

theorem weighted_exponential_density (R W u : ℝ) (hR : 0 < R) (hW : 0 ≤ W) :
    ENNReal.ofReal (W/R)*exponentialPDF R u = ENNReal.ofReal W*activeClockWeight R u := by
  by_cases hu : 0 ≤ u
  · rw [exponentialPDF_of_nonneg hu,activeClockWeight,if_pos hu,exponential_Ioi R u hR hu,
      ← ENNReal.ofReal_mul (div_nonneg hW hR.le),← ENNReal.ofReal_mul hW]
    congr 1
    rw [neg_mul]
    field_simp [ne_of_gt hR]
  · rw [exponentialPDF_of_neg (lt_of_not_ge hu),activeClockWeight,if_neg hu]
    simp only [mul_zero]

variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Single-clock compensator identity. Arbitrary nonnegative time weights
permit translated operating windows and predictable history guards. -/
theorem clock_reward_occupation (rate : β → ℝ) (hr : ∀ j,0 ≤ rate j)
    (hR : 0 < ∑ j,rate j) (w : β → ℝ) (hw : ∀ j,0 ≤ w j)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y,ENNReal.ofReal (w y.1)*g y.2 ∂jumpClockMeasure rate hr hR) =
      ∫⁻ u,g u*ENNReal.ofReal (∑ j,rate j*w j)*activeClockWeight (∑ j,rate j) u := by
  let R := ∑ j,rate j
  let W := ∑ j,rate j*w j
  have hW : 0 ≤ W := Finset.sum_nonneg (fun j _ => mul_nonneg (hr j) (hw j))
  have hpdf : Measurable (exponentialPDF R) := (measurable_exponentialPDFReal R).ennreal_ofReal
  letI := isProbabilityMeasure_expMeasure hR
  unfold jumpClockMeasure
  rw [lintegral_prod_mul (f := fun j => ENNReal.ofReal (w j)) (g := g)
    (measurable_of_countable _).aemeasurable hg.aemeasurable,
    jumpLabel_weight_integral rate hr hR w hw]
  change ENNReal.ofReal (W/R)*(∫⁻ u,g u ∂volume.withDensity (exponentialPDF R)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume hpdf hg]
  simp only [Pi.mul_apply]
  rw [← lintegral_const_mul _ (hpdf.mul hg)]
  apply lintegral_congr
  intro u
  change ENNReal.ofReal (W/R)*(exponentialPDF R u*g u) = _
  rw [← mul_assoc,weighted_exponential_density R W u hR hW]
  ac_rfl

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

theorem jumpState_reward_occupation (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (x : α) (w : β → ℝ) (hw : ∀ j,0 ≤ w j) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y,ENNReal.ofReal (y.2.1.elim (fun _ => 0) w)*g y.2.2
      ∂jumpStateKernel next rate hr ht x) =
    ∫⁻ u,g u*ENNReal.ofReal (∑ j,rate x j*w j)*activeClockWeight (∑ j,rate x j) u := by
  letI := markSingletonClass (β := β)
  change (∫⁻ y,ENNReal.ofReal (y.2.1.elim (fun _ => 0) w)*g y.2.2
    ∂(jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x)) = _
  have hm : Measurable (fun y : JumpState α β =>
      ENNReal.ofReal (y.2.1.elim (fun _ => 0) w)*g y.2.2) :=
    (((measurable_of_countable (fun j : Unit ⊕ β => j.elim (fun _ => 0) w)).comp
      measurable_snd.fst).ennreal_ofReal).mul (hg.comp measurable_snd.snd)
  rw [lintegral_map hm (jumpStateUpdate_measurable next x)]
  exact clock_reward_occupation (rate x) (hr x) (ht x) w hw g hg

/-- The predictable one-clock identity integrated over actual histories.
No compensator law is assumed: the history transition identity supplies it. -/
theorem history_reward_occupation (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (initial : α) (w : α → β → ℝ) (hw : ∀ x j,0 ≤ w x j) (k : ℕ)
    (g : (Finset.Iic k → JumpState α β) → ℝ → ℝ≥0∞)
    (hg : Measurable (fun p : (Finset.Iic k → JumpState α β) × ℝ => g p.1 p.2)) :
    (∫⁻ z,ENNReal.ofReal ((z (k+1)).2.1.elim (fun _ => 0) (w (z k).1))*
      g (Preorder.frestrictLe k z) (z (k+1)).2.2 ∂jumpTrajectoryLaw initial next rate hr ht) =
    ∫⁻ h,(∫⁻ u : ℝ,g h u*
      ENNReal.ofReal (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j*
        w (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j)*
      activeClockWeight (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j) u)
      ∂(jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) := by
  letI := markSingletonClass (β := β)
  let μ := jumpTrajectoryLaw initial next rate hr ht
  let F : (Finset.Iic k → JumpState α β) × JumpState α β → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (p.2.2.1.elim (fun _ => 0) (w (p.1 ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1))*g p.1 p.2.2.2
  have hm : Measurable F := by
    have hl : Measurable (fun p : α × (Unit ⊕ β) => ENNReal.ofReal (p.2.elim (fun _ => 0) (w p.1))) :=
      measurable_of_countable _
    exact (hl.comp ((((measurable_pi_apply (⟨k,Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).comp
      measurable_fst).fst).prodMk measurable_snd.snd.fst)).mul
      (hg.comp (measurable_fst.prodMk measurable_snd.snd.snd))
  have htransition : μ.map (Preorder.frestrictLe k) ⊗ₘ jumpHistoryKernel next rate hr ht k =
      μ.map (fun z => (Preorder.frestrictLe k z,z (k+1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  change (∫⁻ z,F (Preorder.frestrictLe k z,z (k+1)) ∂μ) = _
  rw [← lintegral_map hm (by fun_prop),← htransition,Measure.lintegral_compProd hm]
  apply lintegral_congr
  intro h
  simpa only [F,jumpHistoryKernel,Kernel.comap_apply] using
    (jumpState_reward_occupation next rate hr ht (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
      (w (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1) (hw _)
      (g h) (hg.comp (measurable_const.prodMk measurable_id)))

end
end StartupCount
