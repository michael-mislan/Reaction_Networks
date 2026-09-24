import proofs.CompositionalMemory.JumpLyapunovProducts
import proofs.RandomViability.JumpInitial

namespace CompositionalMemory
open RandomViability MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def lyapunovCrossingBy {α β : Type*} (V : α → ℝ) (B T : ℝ) (K : ℕ)
    (z : ℕ → JumpState α β) : Prop :=
  ∃ j, j ≤ K ∧ (∑ i ∈ Finset.range j,(z (i+1)).2.2) ≤ T ∧ B ≤ V (z j).1

variable {α β : Type*}
  [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem jump_lyapunov_crossing_by (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (V : α → ℝ) (hV : ∀ x, 0 < V x) (c : ℝ) (hc : 0 ≤ c)
    (hgen : ∀ x, (∑ b, rate x b*(V (next x b)-V x)) ≤ c*V x)
    (B T : ℝ) (hB : 0 < B) (K : ℕ) :
    jumpTrajectoryLaw initial next rate hr ht {z | lyapunovCrossingBy V B T K z} ≤
      ENNReal.ofReal (V initial*Real.exp (c*T)/B) := by
  let μ := jumpTrajectoryLaw initial next rate hr ht
  let a := ENNReal.ofReal (B/V initial*Real.exp (-c*T))
  let C := ENNReal.ofReal (V initial*Real.exp (c*T)/B)
  have hb := predictable_product_crossing_bound μ (jumpHistoryKernel next rate hr ht)
    (fun _ => Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure)
    (lyapunovMultiplier V c) (lyapunovMultiplier_measurable V c)
    (lyapunovMultiplier_mean next rate hr ht V hV c hc hgen) a K
  have hsub : μ {z | lyapunovCrossingBy V B T K z} ≤
      μ {z | ∃ j, j ≤ K ∧ a ≤ trajectoryProduct (lyapunovMultiplier V c) j z} := by
    apply measure_mono_ae
    filter_upwards [jumpTrajectory_initial_population initial next rate hr ht] with z hz
    rintro ⟨j,hj,hT,hval⟩
    refine ⟨j,hj,?_⟩
    rw [lyapunov_product_formula V hV c z j,hz]
    apply ENNReal.ofReal_le_ofReal
    have hr := div_le_div_of_nonneg_right hval (hV initial).le
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hT (neg_nonpos.mpr hc))
    exact mul_le_mul hr he (Real.exp_pos _).le (div_pos (hV _) (hV initial)).le
  have hweighted := (mul_le_mul_right hsub a).trans hb
  have hVi := hV initial
  have hCa : C*a=1 := by
    dsimp [C,a]
    rw [← ENNReal.ofReal_mul (by positivity)]
    have he : V initial*Real.exp (c*T)/B*(B/V initial*Real.exp (-c*T))=1 := by
      rw [neg_mul,Real.exp_neg]
      field_simp [ne_of_gt hB,ne_of_gt (hV initial)]
    rw [he,ENNReal.ofReal_one]
  calc
    _ = C*(a*μ {z | lyapunovCrossingBy V B T K z}) := by rw [← mul_assoc,hCa,one_mul]
    _ ≤ C*1 := mul_le_mul_right hweighted C
    _ = _ := mul_one C

theorem jump_lyapunov_crossing_any (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (V : α → ℝ) (hV : ∀ x, 0 < V x) (c : ℝ) (hc : 0 ≤ c)
    (hgen : ∀ x, (∑ b, rate x b*(V (next x b)-V x)) ≤ c*V x)
    (B T : ℝ) (hB : 0 < B) :
    jumpTrajectoryLaw initial next rate hr ht (⋃ K, {z | lyapunovCrossingBy V B T K z}) ≤
      ENNReal.ofReal (V initial*Real.exp (c*T)/B) := by
  have hm : Monotone (fun K => {z : ℕ → JumpState α β | lyapunovCrossingBy V B T K z}) := by
    intro K L hKL z hz
    obtain ⟨j,hj,hT,hval⟩ := hz
    exact ⟨j,hj.trans hKL,hT,hval⟩
  rw [hm.measure_iUnion]
  exact iSup_le (fun K => jump_lyapunov_crossing_by initial next rate hr ht V hV c hc hgen B T hB K)

end CompositionalMemory
