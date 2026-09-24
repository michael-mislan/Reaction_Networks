import proofs.RandomViability.JumpStateLaplace

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000

variable {β : Type*} [Fintype β]

/-- The Taylor bound uses the literal quadratic rate, without counting channels. -/
theorem rate_exponential_tilt_bound (a d : β → ℝ) (ha : ∀ i, 0 ≤ a i)
    (θ : ℝ) (hsmall : ∀ i, |θ*d i| ≤ 1) :
    (∑ i, a i*(Real.exp (θ*d i)-1)) ≤
      θ*(∑ i,a i*d i)+θ^2*(∑ i,a i*(d i)^2) := by
  have hp (i) : Real.exp (θ*d i)-1 ≤ θ*d i+θ^2*(d i)^2 := by
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hsmall i))).2
    nlinarith only [h]
  calc
    _ ≤ ∑ i,a i*(θ*d i+θ^2*(d i)^2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hp i) (ha i))
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem tilted_total_positive (a d : β → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ht : 0 < ∑ i,a i) (θ : ℝ) : 0 < ∑ i,a i*Real.exp (θ*d i) := by
  obtain ⟨i,hi⟩ : ∃ i,a i > 0 := by
    by_contra h
    push Not at h
    have hz := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => h i)
    linarith
  exact Finset.sum_pos' (fun j _ => mul_nonneg (ha j) (Real.exp_pos _).le)
    ⟨i,Finset.mem_univ i,mul_pos hi (Real.exp_pos _)⟩

variable [MeasurableSpace β] [MeasurableSingletonClass β]

theorem stateDependentMultiplier_measurable {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α] (w : α → β → ℝ) (s : α → ℝ) :
    Measurable (fun p : α × JumpState α β => jumpMultiplier (w p.1) (s p.1) p.2) :=
  measurable_from_prod_countable_right (fun x => jumpMultiplier_measurable (w x) (s x))

def stoppedStateMultiplier {α : Type*} (w : α → β → ℝ) (s : α → ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState α β) (y : JumpState α β) : ℝ≥0∞ :=
  if stop k h then 1 else
    jumpMultiplier (w (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)
      (s (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1) y

theorem stoppedStateMultiplier_measurable {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α] (w : α → β → ℝ) (s : α → ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState α β) × JumpState α β =>
      stoppedStateMultiplier w s stop k p.1 p.2) := by
  have hx : Measurable (fun h : Finset.Iic k → JumpState α β =>
      (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1) := (measurable_pi_apply _).fst
  exact Measurable.ite ((hstop k).preimage measurable_fst) measurable_const
    ((stateDependentMultiplier_measurable w s).comp
      ((hx.comp measurable_fst).prodMk measurable_snd))

/-- Exact exponential clocks turn the generator estimate into a one-step
nonnegative multiplier with expectation at most one, including negative drift. -/
theorem jumpClock_exponential_tilt_le_one (a d : β → ℝ) (ha : ∀ i,0 ≤ a i)
    (ht : 0 < ∑ i,a i) (θ s : ℝ)
    (hs : (∑ i,a i*(Real.exp (θ*d i)-1)) ≤ s) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (θ*d y.1)) *
      ENNReal.ofReal (Real.exp (-s*y.2)) ∂jumpClockMeasure a ha ht) ≤ 1 := by
  have he : (∑ i,a i*Real.exp (θ*d i))-(∑ i,a i) =
      ∑ i,a i*(Real.exp (θ*d i)-1) := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
  have hb : (∑ i,a i*Real.exp (θ*d i)) ≤ (∑ i,a i)+s := by linarith
  have hp : 0 < (∑ i,a i)+s := (tilted_total_positive a d ha ht θ).trans_le hb
  rw [jumpClock_weight_laplace a ha ht (fun i => Real.exp (θ*d i))
    (fun _ => (Real.exp_pos _).le) s hp]
  apply (ENNReal.ofReal_le_one).mpr
  exact (div_le_one hp).mpr hb

theorem jumpState_exponential_tilt_le_one {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x i,0 ≤ rate x i) (ht : ∀ x,0 < ∑ i,rate x i)
    (x : α) (d : β → ℝ) (θ s : ℝ)
    (hs : (∑ i,rate x i*(Real.exp (θ*d i)-1)) ≤ s) :
    (∫⁻ y, jumpMultiplier (fun i => Real.exp (θ*d i)) s y
      ∂jumpStateKernel next rate hr ht x) ≤ 1 := by
  change (∫⁻ y, jumpMultiplier (fun i => Real.exp (θ*d i)) s y
    ∂(jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x)) ≤ 1
  rw [lintegral_map (jumpMultiplier_measurable _ _) (jumpStateUpdate_measurable next x)]
  exact jumpClock_exponential_tilt_le_one (rate x) d (hr x) (ht x) θ s hs

end
end RandomViability
