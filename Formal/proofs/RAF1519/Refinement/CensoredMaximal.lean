import proofs.RAF1519.Refinement.CensoredTime
import proofs.RandomViability.JumpWaitingSupport

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal
variable {α β : Type*} [Fintype β]

def coordinateFluctuationBy (rate inc : α → β → ℝ) (good : Set α) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (δ : ℝ) (K : ℕ) (z : ℕ → JumpState α β) : Prop :=
  ∃ j,j ≤ K ∧ δ ≤ ∑ i : Fin j,coordinateCompensation rate inc good T stop
    i (Preorder.frestrictLe (i:ℕ) z) (z ((i:ℕ)+1))

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

theorem coordinate_crossing_tail (initial : α) (next : α → β → α) (rate inc : α → β → ℝ)
    (hr : ∀ x a,0 ≤ rate x a) (ht : ∀ x,0 < ∑ a,rate x a)
    (good : Set α) (θ v T : ℝ) (hθ : 0 ≤ θ) (hv : 0 ≤ v) (hT : 0 ≤ T)
    (hsmall : ∀ x ∈ good, ∀ a, |θ*inc x a| ≤ 1)
    (hvar : ∀ x ∈ good, (∑ a,rate x a*(inc x a)^2) ≤ v)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (δ : ℝ) (K : ℕ) :
    jumpTrajectoryLaw initial next rate hr ht
      {z | coordinateFluctuationBy rate inc good T stop δ K z} ≤
      ENNReal.ofReal (Real.exp (-θ*δ+θ^2*v*T)) := by
  let μ := jumpTrajectoryLaw initial next rate hr ht
  let κ := jumpHistoryKernel next rate hr ht
  let m := coordinateMultiplier rate inc good θ v T stop
  let L := θ*δ-θ^2*v*T
  let a := ENNReal.ofReal (Real.exp L)
  let B := ENNReal.ofReal (Real.exp (-L))
  let W : Set (ℕ → JumpState α β) := {z | ∀ i,0 ≤ (z (i+1)).2.2}
  have hw : ∀ᵐ z ∂μ,z ∈ W := jumpTrajectory_wait_nonneg initial next rate hr ht
  have hc := predictable_product_crossing_bound μ κ
    (fun _ => Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure)
    m (coordinateMultiplier_measurable rate inc good θ v T stop hstop)
    (coordinate_multiplier_mean next rate inc hr ht good θ v T hsmall hvar stop) a K
  have hsub : W ∩ {z | coordinateFluctuationBy rate inc good T stop δ K z} ⊆
      {z | ∃ j,j ≤ K ∧ a ≤ trajectoryProduct m j z} := by
    intro z hz
    obtain ⟨j,hj,hA⟩ := hz.2
    refine ⟨j,hj,?_⟩
    dsimp only [m,a]
    rw [coordinate_product_exp]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have htime := coordinate_time_bound good T hT stop z hz.1 j
    exact sub_le_sub (mul_le_mul_of_nonneg_left hA hθ)
      (mul_le_mul_of_nonneg_left htime (by positivity))
  have heq : μ (W ∩ {z | coordinateFluctuationBy rate inc good T stop δ K z}) =
      μ {z | coordinateFluctuationBy rate inc good T stop δ K z} :=
    Measure.measure_inter_eq_of_ae hw
  have hb : a*μ {z | coordinateFluctuationBy rate inc good T stop δ K z} ≤ 1 := by
    rw [← heq]
    exact (mul_le_mul_right (measure_mono hsub) a).trans hc
  have hinv : B*a = 1 := by
    dsimp [B,a]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,neg_add_cancel,
      Real.exp_zero,ENNReal.ofReal_one]
  have hbound : μ {z | coordinateFluctuationBy rate inc good T stop δ K z} ≤ B := by
    calc
      _ = B*(a*μ {z | coordinateFluctuationBy rate inc good T stop δ K z}) := by
        rw [← mul_assoc,hinv,one_mul]
      _ ≤ B*1 := mul_le_mul_right hb B
      _ = _ := mul_one _
  have he : -L = -θ*δ+θ^2*v*T := by dsimp [L]; ring
  simpa only [B,he] using hbound

theorem coordinate_any_index_tail (initial : α) (next : α → β → α) (rate inc : α → β → ℝ)
    (hr : ∀ x a,0 ≤ rate x a) (ht : ∀ x,0 < ∑ a,rate x a)
    (good : Set α) (θ v T : ℝ) (hθ : 0 ≤ θ) (hv : 0 ≤ v) (hT : 0 ≤ T)
    (hsmall : ∀ x ∈ good, ∀ a, |θ*inc x a| ≤ 1)
    (hvar : ∀ x ∈ good, (∑ a,rate x a*(inc x a)^2) ≤ v)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (δ : ℝ) :
    jumpTrajectoryLaw initial next rate hr ht
      (⋃ K,{z | coordinateFluctuationBy rate inc good T stop δ K z}) ≤
      ENNReal.ofReal (Real.exp (-θ*δ+θ^2*v*T)) := by
  have hm : Monotone (fun K => {z | coordinateFluctuationBy rate inc good T stop δ K z}) := by
    intro K J hK z hz
    obtain ⟨j,hj,hA⟩ := hz
    exact ⟨j,hj.trans hK,hA⟩
  rw [hm.measure_iUnion]
  exact iSup_le (fun K => coordinate_crossing_tail initial next rate inc hr ht good θ v T
    hθ hv hT hsmall hvar stop hstop δ K)

end
end RAF1519.Refinement
